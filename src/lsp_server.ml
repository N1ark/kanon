(** The language server of Kanon, [kanon lsp]: it checks the languages of the
    open files as they are edited, reports their errors, and answers definition,
    hover, completion and symbol requests from the items parsed by the last
    check.

    A [.kn] file is only meaningful in its language, so the server finds the
    {e roots} of the workspace, the [.knl] files that no other file uses (e.g.
    [lang.knl]), and checks a file as part of each root whose modules contain
    it, as [kanon ocaml root.knl] would. *)

module R = Lsp_rpc

(** {1 Texts} *)

type text = { s : string; lines : int array  (** the offsets of the lines *) }

let text s =
  let l = ref [ 0 ] in
  String.iteri (fun i c -> if c = '\n' then l := (i + 1) :: !l) s;
  { s; lines = Array.of_list (List.rev !l) }

(** The line of the offset [o]. *)
let line_of t o =
  let rec go lo hi =
    (* lines.(lo) <= o < lines.(hi) *)
    if hi - lo <= 1 then lo
    else
      let mid = (lo + hi) / 2 in
      if t.lines.(mid) <= o then go mid hi else go lo mid
  in
  go 0 (Array.length t.lines)

(** The UTF-16 code units of the UTF-8 bytes of [s] from [a] to [b], excluded.
*)
let utf16 s a b =
  let n = ref 0 in
  for i = a to b - 1 do
    let c = Char.code s.[i] in
    if c < 0x80 || (c >= 0xC0 && c < 0xF0) then incr n
    else if c >= 0xF0 then n := !n + 2
  done;
  !n

let position t o : Yojson.Safe.t =
  let o = max 0 (min o (String.length t.s)) in
  let l = line_of t o in
  `Assoc [ ("line", `Int l); ("character", `Int (utf16 t.s t.lines.(l) o)) ]

(** The offset of an LSP position. *)
let offset t ~line ~character =
  if line < 0 then 0
  else if line >= Array.length t.lines then String.length t.s
  else
    let n = String.length t.s in
    let rec go i units =
      if i >= n || t.s.[i] = '\n' || units >= character then i
      else go (i + 1) (units + utf16 t.s i (i + 1))
    in
    go t.lines.(line) 0

let range t (a, b) : Yojson.Safe.t =
  `Assoc [ ("start", position t a); ("end", position t b) ]

let is_word_char = function
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

(** The word at the offset [o], or just before it. *)
let word_at s o =
  let n = String.length s in
  let o =
    if o < n && is_word_char s.[o] then o
    else if o > 0 && o <= n && is_word_char s.[o - 1] then o - 1
    else -1
  in
  if o < 0 then (0, 0)
  else
    let a = ref o and b = ref o in
    while !a > 0 && is_word_char s.[!a - 1] do
      decr a
    done;
    while !b < n && is_word_char s.[!b] do
      incr b
    done;
    (!a, !b)

(** The span of the word [x] in [s], from the offset [a] on, before [b]. *)
let find_word s a b x =
  let n = String.length x and b = min b (String.length s) in
  let rec go i =
    if i + n > b then (a, a)
    else if
      String.sub s i n = x
      && (i = 0 || not (is_word_char s.[i - 1]))
      && (i + n >= String.length s || not (is_word_char s.[i + n]))
    then (i, i + n)
    else go (i + 1)
  in
  go a

let sub s (a, b) =
  let a = max 0 a and b = min b (String.length s) in
  if b <= a then "" else String.sub s a (b - a)

(** At most [n] lines of [s]. *)
let clip n s =
  match String.split_on_char '\n' s with
  | l when List.length l <= n -> s
  | l -> String.concat "\n" (List.filteri (fun i _ -> i < n) l) ^ "\n..."

(** [s] on one line, shortened. *)
let one_line s =
  let s =
    String.concat " "
      (List.filter (( <> ) "")
         (String.split_on_char ' '
            (String.map (function '\n' | '\t' | '\r' -> ' ' | c -> c) s)))
  in
  if String.length s > 120 then String.sub s 0 117 ^ "..." else s

(** {1 Files} *)

(** The open documents, by path, with their text. *)
let docs : (string, string) Hashtbl.t = Hashtbl.create 16

let read_disk f =
  try Some (In_channel.with_open_bin f In_channel.input_all)
  with Sys_error _ -> None

(** The contents of [f]: its open document, the file on disk, or a built-in
    module ([+bool.kn]). *)
let contents f =
  match Loader.builtin f with
  | Some name -> List.assoc_opt name Builtin.files
  | None -> (
      match Hashtbl.find_opt docs f with
      | Some s -> Some s
      | None -> read_disk f)

let exists f = Hashtbl.mem docs f || Sys.file_exists f

(** {1 Projects} *)

(** The folders of the workspace. *)
let folders : string list ref = ref []

(** The [.kn] and [.knl] files of the workspace. *)
let files : string list ref = ref []

(** The files that each file uses, from a scan of its [use]s. *)
let graph : (string, string list) Hashtbl.t = Hashtbl.create 64

(** The sources of the built-in modules in the workspace, by their names
    ([+bool.kn]): the files of Kanon's [modules/], which stand for them, so that
    they are checked with the languages that use them as they are edited. *)
let builtin_sources : (string, string) Hashtbl.t = Hashtbl.create 4

let resolve f = Option.value (Hashtbl.find_opt builtin_sources f) ~default:f

let skipped_dir d =
  List.mem d [ "_build"; "node_modules"; "_opam"; "target" ]
  || (d <> "" && d.[0] = '.')

let is_kanon f = Filename.check_suffix f ".kn" || Filename.check_suffix f ".knl"

let rec walk dir acc =
  Array.fold_left
    (fun acc n ->
      let p = Filename.concat dir n in
      (* links to directories are not followed, as they may loop *)
      match (Unix.lstat p).st_kind with
      | S_DIR -> if skipped_dir n then acc else walk p acc
      | (S_REG | S_LNK) when is_kanon n && Sys.file_exists p -> p :: acc
      | _ -> acc
      | exception Unix.Unix_error _ -> acc)
    acc
    (try Sys.readdir dir with Sys_error _ -> [||])

(** The files that [f] uses, from its tokens (without parsing it, which needs
    the infix words of its language). *)
let scan_uses f =
  match contents f with
  | None -> []
  | Some s ->
      let lb = Lexing.from_string s in
      let rec go acc =
        match Kanon_lexer.token lb with
        | Kanon_parser.EOF -> List.rev acc
        | USE -> (
            match Kanon_lexer.token lb with
            | STRING m -> go (m :: acc)
            | PLUS -> (
                match Kanon_lexer.token lb with
                | LID m -> go (("+" ^ m) :: acc)
                | _ -> go acc)
            | EOF -> List.rev acc
            | _ -> go acc)
        | _ -> go acc
        | exception Kanon_lexer.Error _ -> go acc
        | exception _ -> List.rev acc
      in
      List.concat_map
        (fun m ->
          List.filter exists
            (List.map resolve
               (snd (Loader.module_files (Filename.dirname f) m))))
        (go [])

let edges f =
  match Hashtbl.find_opt graph f with
  | Some l -> l
  | None ->
      let l = scan_uses f in
      Hashtbl.replace graph f l;
      l

let rescan () =
  files := List.concat_map (fun d -> walk d []) !folders;
  Hashtbl.reset builtin_sources;
  List.iter
    (fun f ->
      let name = Filename.basename f in
      if
        Filename.basename (Filename.dirname f) = "modules"
        && List.mem_assoc name Builtin.files
      then Hashtbl.replace builtin_sources ("+" ^ name) f)
    !files;
  Hashtbl.reset graph;
  List.iter (fun f -> ignore (edges f)) !files;
  Hashtbl.iter (fun f _ -> ignore (edges f)) docs

(** The files that [fs] use, transitively, with [fs]. *)
let closure fs =
  let seen = Hashtbl.create 16 in
  let rec go f =
    if not (Hashtbl.mem seen f) then (
      Hashtbl.add seen f ();
      List.iter go (edges f))
  in
  List.iter go fs;
  List.sort compare (Hashtbl.fold (fun f () l -> f :: l) seen [])

(** The [.knl] files that no other file uses. *)
let roots () =
  let used = Hashtbl.create 64 in
  Hashtbl.iter
    (fun _ l -> List.iter (fun f -> Hashtbl.replace used f ()) l)
    graph;
  List.sort_uniq compare
    (List.filter
       (fun f -> Filename.check_suffix f ".knl" && not (Hashtbl.mem used f))
       (!files @ Hashtbl.fold (fun f _ l -> f :: l) docs []))

(** The {e units} that the file [f] is checked in: the arguments of [kanon] that
    check it. Those are the roots that use it; or, for a [.kn] file that no root
    uses, the only root of its directory with it; or else [f] alone. *)
let units_of f =
  let roots = roots () in
  match List.filter (fun r -> List.mem f (closure [ r ])) roots with
  | _ :: _ as rs -> List.map (fun r -> [ r ]) rs
  | [] -> (
      let here = Filename.dirname f in
      match List.filter (fun r -> Filename.dirname r = here) roots with
      | [ r ] when Filename.check_suffix f ".kn" -> [ [ r; f ] ]
      | _ -> [ [ f ] ])

(** {1 Definitions} *)

type kind =
  | Fn
  | Rule
  | Prim
  | Oracle
  | Node
  | Constr
  | Type of bool  (** whether it is a record *)
  | Operator
  | Label of string  (** a rule of the function *)
  | Extend  (** [extend rule f], whose rules are its children *)

type def = {
  name : string;
  kind : kind;
  file : string;
  sel : int * int;  (** the span of its name *)
  item : int * int;  (** the span of the item *)
  header : string;  (** its source, or that of its header *)
  children : def list;  (** the rules of a rule, the constructors of a type *)
}

(** The definitions of each file, from the last check that parsed it. *)
let index : (string, text * def list) Hashtbl.t = Hashtbl.create 64

let rec flat d = d :: List.concat_map flat d.children

let span (loc : Ppxlib.Location.t) =
  (loc.loc_start.pos_cnum, loc.loc_end.pos_cnum)

(** The header of the item spanning [(a, b)]: up to the [=] of its body. *)
let header s (a, b) =
  let b = min b (String.length s) in
  let rec go i depth =
    if i >= b then b
    else
      match s.[i] with
      | '(' | '[' | '{' -> go (i + 1) (depth + 1)
      | ')' | ']' | '}' -> go (i + 1) (depth - 1)
      | '"' -> (
          match String.index_from_opt s (i + 1) '"' with
          | Some j -> go (j + 1) depth
          | None -> b)
      | '=' when depth = 0 && (i + 1 >= b || s.[i + 1] <> '=') -> i
      | _ -> go (i + 1) depth
  in
  String.trim (sub s (a, go a 0))

(** The comment just before the offset [a], without a blank line in between. *)
let doc_comment s a =
  let rec back i nl =
    if i < 0 then None
    else
      match s.[i] with
      | '\n' -> if nl then None else back (i - 1) true
      | ' ' | '\t' | '\r' -> back (i - 1) nl
      | _ -> Some i
  in
  let rec opening i depth =
    if i < 1 then None
    else if s.[i - 1] = '(' && s.[i] = '*' then
      if depth = 0 then Some (i - 1) else opening (i - 2) (depth - 1)
    else if s.[i - 1] = '*' && s.[i] = ')' then opening (i - 2) (depth + 1)
    else opening (i - 1) depth
  in
  match back (a - 1) false with
  | Some j when j >= 3 && s.[j] = ')' && s.[j - 1] = '*' -> (
      match opening (j - 2) 0 with
      | Some k ->
          let lines = String.split_on_char '\n' (sub s (k + 2, j - 1)) in
          let indent l =
            let n = String.length l in
            let rec go i = if i < n && l.[i] = ' ' then go (i + 1) else i in
            if String.trim l = "" then max_int else go 0
          in
          let d =
            List.fold_left (fun m l -> min m (indent l)) max_int (List.tl lines)
          in
          let strip l =
            if String.length l >= d then String.sub l d (String.length l - d)
            else String.trim l
          in
          Some
            (String.trim
               (String.concat "\n"
                  (String.trim (List.hd lines) :: List.map strip (List.tl lines))))
      | None -> None)
  | _ -> None

let attr_string name (attrs : Ppxlib.attributes) =
  List.find_map
    (fun (a : Ppxlib.attribute) ->
      if a.attr_name.txt <> name then None
      else
        match a.attr_payload with
        | PStr
            [
              {
                pstr_desc =
                  Pstr_eval
                    ( { pexp_desc = Pexp_constant (Pconst_string (s, _, _)); _ },
                      _ );
                _;
              };
            ] ->
            Some s
        | _ -> None)
    attrs

(** The rules of the cases [cs] of the function [f]. *)
let labels file s f (cs : Ppxlib.case list) =
  List.concat_map
    (fun (c : Ppxlib.case) ->
      List.filter_map
        (fun (a : Ppxlib.attribute) ->
          match (a.attr_name.txt, a.attr_payload) with
          | ( "r",
              PStr
                [
                  {
                    pstr_desc =
                      Pstr_eval
                        ({ pexp_desc = Pexp_ident { txt = id; _ }; _ }, _);
                    _;
                  };
                ] ) ->
              let sel = span a.attr_loc in
              let eol =
                Option.value
                  (String.index_from_opt s (fst sel) '\n')
                  ~default:(String.length s)
              in
              Some
                {
                  name = Ppxlib.Longident.name id;
                  kind = Label f;
                  file;
                  sel;
                  item = (fst sel, max eol (snd (span c.pc_rhs.pexp_loc)));
                  header = String.trim (sub s (fst sel, eol));
                  children = [];
                }
          | _ -> None)
        c.pc_lhs.ppat_attributes)
    cs

(** The cases of a rule function, from its body. *)
let rec rule_cases (e : Ppxlib.expression) =
  match e.pexp_desc with
  | Pexp_function (_, _, Pfunction_body b) -> rule_cases b
  | Pexp_match
      ({ pexp_desc = Pexp_extension ({ txt = "kanon.operands"; _ }, _); _ }, cs)
    ->
      cs
  | _ -> []

(** The definitions of the items [str] of the file [file], of text [s]. *)
let defs_of file s (str : Ppxlib.structure) =
  List.concat_map
    (fun (si : Ppxlib.structure_item) ->
      let item = span si.pstr_loc in
      let mk ?(children = []) ?(header = clip 10 (String.trim (sub s item)))
          name kind sel =
        { name; kind; file; sel; item; header; children }
      in
      let named x = find_word s (fst item) (snd item) x in
      match si.pstr_desc with
      | Pstr_value
          ( _,
            [
              {
                pvb_pat = { ppat_desc = Ppat_var { txt = x; _ }; _ };
                pvb_attributes;
                pvb_expr;
                _;
              };
            ] ) ->
          if
            List.exists
              (fun (a : Ppxlib.attribute) -> a.attr_name.txt = "spec")
              pvb_attributes
          then
            [
              mk ~header:(header s item)
                ~children:(labels file s x (rule_cases pvb_expr))
                x Rule (named x);
            ]
          else [ mk ~header:(header s item) x Fn (named x) ]
      | Pstr_primitive vd ->
          let x = vd.pval_name.txt in
          [
            mk x
              (if vd.pval_prim = [ "oracle" ] then Oracle else Prim)
              (named x);
          ]
      | Pstr_type
          ( _,
            [
              {
                ptype_name = { txt = "node"; _ };
                ptype_kind = Ptype_variant [ cd ];
                _;
              };
            ] ) ->
          [ mk cd.pcd_name.txt Node (span cd.pcd_name.loc) ]
      | Pstr_type (_, [ td ]) ->
          let cds = match td.ptype_kind with Ptype_variant l -> l | _ -> [] in
          let constr (cd : Ppxlib.constructor_declaration) =
            {
              name = cd.pcd_name.txt;
              kind = Constr;
              file;
              sel = span cd.pcd_name.loc;
              item = span cd.pcd_loc;
              header = clip 10 (String.trim (sub s (span cd.pcd_loc)));
              children = [];
            }
          in
          let record =
            match td.ptype_kind with Ptype_record _ -> true | _ -> false
          in
          [
            mk ~children:(List.map constr cds) td.ptype_name.txt (Type record)
              (span td.ptype_name.loc);
          ]
      | Pstr_eval (e, attrs) -> (
          match
            ( attr_string "infix" attrs,
              attr_string "prefix" attrs,
              attr_string "extend" attrs,
              e.pexp_desc )
          with
          | Some op, _, _, _ | None, Some op, _, _ ->
              let sel =
                match find_word s (fst item) (snd item) ("\"" ^ op ^ "\"") with
                | a, b when b > a -> (a + 1, b - 1)
                | _ -> (fst item, fst item)
              in
              [ mk op Operator sel ]
          | None, None, Some f, Pexp_function (_, _, Pfunction_cases (cs, _, _))
            ->
              [
                mk ~header:(header s item) ~children:(labels file s f cs) f
                  Extend (named f);
              ]
          | _ -> [])
      | _ -> [])
    str

(** {1 Checks} *)

(** The results of the last check of each unit: the files it reads, and its
    errors, by file. *)
let results :
    (string list, string list * (string * Yojson.Safe.t) list) Hashtbl.t =
  Hashtbl.create 8

(** The diagnostics last published for each file. *)
let published : (string, Yojson.Safe.t list) Hashtbl.t = Hashtbl.create 16

(** The files changed since the last check. *)
let dirty : string list ref = ref []

let error_diag t sel message : Yojson.Safe.t =
  `Assoc
    [
      ("range", range t sel);
      ("severity", `Int 1);
      ("source", `String "kanon");
      ("message", `String message);
    ]

(** Checks the unit [u], as [kanon] does, and indexes the files it parses. *)
let check_unit u =
  let main = List.hd u in
  let texts = Hashtbl.create 16 in
  let read f =
    match Hashtbl.find_opt texts f with
    | Some t -> Option.map (fun t -> t.s) t
    | None ->
        let t = Option.map text (contents f) in
        Hashtbl.add texts f t;
        Option.map (fun t -> t.s) t
  in
  let text_of f =
    match Hashtbl.find_opt texts f with
    | Some t -> t
    | None -> Option.map text (contents f)
  in
  let parsed = ref [] in
  let at_main msg = (main, error_diag (text "") (0, 0) msg) in
  let diag (loc : Ppxlib.Location.t) msg =
    let f = loc.loc_start.pos_fname in
    match if Filename.is_relative f then None else text_of f with
    | Some t ->
        let a, b = span loc in
        (* a point (a syntax error): the word or character there, or the last
           one before the end of its line *)
        let a, b =
          if b > a then (a, b)
          else
            match word_at t.s a with
            | a', b' when a' = a && b' > a -> (a, b')
            | _ when a < String.length t.s && t.s.[a] <> '\n' -> (a, a + 1)
            | _ ->
                let rec last i =
                  if i < 0 then (a, a)
                  else
                    match t.s.[i] with
                    | ' ' | '\t' | '\r' | '\n' -> last (i - 1)
                    | _ -> (i, i + 1)
                in
                last (a - 1)
        in
        (f, error_diag t (a, b) msg)
    | None ->
        at_main
          (if f = "" || f = "_none_" then msg
           else Format.asprintf "%a: %s" Check.pp_loc loc msg)
  in
  let diags =
    Check.reset ();
    let t0 = Unix.gettimeofday () in
    let diags =
      try
        let langs, rules =
          Loader.load ~read ~resolve
            ~on_parse:(fun f str -> parsed := (f, str) :: !parsed)
            u
        in
        if langs <> [] then (
          Check.language (List.concat_map snd langs);
          if rules <> [] then ignore (Check.program (List.concat_map snd rules)));
        []
      with
      | Check.Error (loc, msg) | Loader.Missing (loc, msg) -> [ (loc, msg) ]
      | e ->
          [
            ( Ppxlib.Location.none,
              "kanon: internal error: " ^ Printexc.to_string e );
          ]
    in
    R.log "kanon lsp: checked %s in %.0fms" (String.concat " " u)
      ((Unix.gettimeofday () -. t0) *. 1000.);
    diags
  in
  List.iter
    (fun (f, str) ->
      match text_of f with
      | Some t -> Hashtbl.replace index f (t, defs_of f t.s str)
      | None -> ())
    !parsed;
  let diags =
    List.concat_map
      (fun ((loc : Ppxlib.Location.t), msg) ->
        (* [x is defined twice] has no location: report the definitions after
           the first *)
        let twice = " is defined twice" in
        let defs =
          if
            (loc.loc_start.pos_fname <> ""
            && loc.loc_start.pos_fname <> "_none_")
            || not (String.ends_with ~suffix:twice msg)
          then []
          else
            let x =
              String.sub msg 0 (String.length msg - String.length twice)
            in
            List.concat_map
              (fun (f, _) ->
                match Hashtbl.find_opt index f with
                | Some (t, defs) when not (Filename.is_relative f) ->
                    List.filter_map
                      (fun d ->
                        match d.kind with
                        | (Fn | Rule | Prim | Oracle) when d.name = x ->
                            Some (f, error_diag t d.sel msg)
                        | _ -> None)
                      defs
                | _ -> [])
              (List.rev !parsed)
        in
        match defs with _ :: (_ :: _ as l) -> l | _ -> [ diag loc msg ])
      diags
  in
  let files =
    List.sort_uniq compare
      (closure u @ List.map fst !parsed @ List.map fst diags)
  in
  (files, diags)

let publish f =
  if not (Filename.is_relative f) then
    let diags =
      Hashtbl.fold
        (fun _ (fs, ds) acc ->
          if List.mem f fs then
            List.filter_map (fun (g, d) -> if g = f then Some d else None) ds
            @ acc
          else acc)
        results []
    in
    let diags = List.sort_uniq compare diags in
    if Option.value (Hashtbl.find_opt published f) ~default:[] <> diags then (
      Hashtbl.replace published f diags;
      R.notify "textDocument/publishDiagnostics"
        (`Assoc
           [ ("uri", `String (R.uri_of_path f)); ("diagnostics", `List diags) ]))

(** Checks the units of the files changed since the last check, and publishes
    the diagnostics of their files. *)
let check () =
  if !dirty <> [] then (
    let changed = List.sort_uniq compare !dirty in
    dirty := [];
    let affected = ref [] in
    (* the units that are no longer units, e.g. a root that is now used *)
    Hashtbl.filter_map_inplace
      (fun u (fs, ds) ->
        if List.mem u (units_of (List.nth u (List.length u - 1))) then
          Some (fs, ds)
        else (
          affected := fs @ !affected;
          None))
      results;
    List.iter
      (fun u ->
        Option.iter
          (fun (fs, _) -> affected := fs @ !affected)
          (Hashtbl.find_opt results u);
        let fs, ds = check_unit u in
        Hashtbl.replace results u (fs, ds);
        affected := fs @ !affected)
      (List.sort_uniq compare (List.concat_map units_of changed));
    List.iter publish (List.sort_uniq compare !affected))

(** {1 Requests} *)

(** The files of the language of [f]: those its units read. *)
let lang_files f =
  let fs =
    List.concat_map
      (fun u -> Option.fold ~none:[] ~some:fst (Hashtbl.find_opt results u))
      (units_of f)
  in
  if fs = [] then Hashtbl.fold (fun f _ l -> f :: l) index []
  else List.sort_uniq compare fs

let lang_defs f =
  List.concat_map
    (fun f ->
      match Hashtbl.find_opt index f with
      | Some (_, defs) -> List.concat_map flat defs
      | None -> [])
    (lang_files f)

(** The function [f] of [extend rule f before], if the text just before the
    offset [a] of [s] is that. *)
let before_of s a =
  let bol =
    match String.rindex_from_opt s (max 0 (a - 1)) '\n' with
    | Some i -> i + 1
    | None -> 0
  in
  let words =
    List.filter (( <> ) "")
      (String.split_on_char ' '
         (String.map (function '\t' -> ' ' | c -> c) (sub s (bol, a))))
  in
  match List.rev words with
  | "before" :: f :: ("rule" | "fn") :: "extend" :: _ -> Some f
  | _ -> None

(** The definitions of the word at the offset [o] of the file [f], and its span.
*)
let resolve f o =
  match contents f with
  | None -> ([], (0, 0))
  | Some s ->
      let w = word_at s o in
      let x = sub s w in
      if x = "" then ([], w)
      else
        let defs = List.filter (fun d -> d.name = x) (lang_defs f) in
        let rules g = List.filter (fun d -> d.kind = Label g) defs in
        let first l =
          Option.value ~default:[]
            (List.find_map
               (fun p ->
                 match List.filter (fun d -> p d.kind) defs with
                 | [] -> None
                 | l -> Some l)
               l)
        in
        let found =
          match before_of s (fst w) with
          | Some g -> rules g
          | None when Char.uppercase_ascii x.[0] = x.[0] && x.[0] <> '_' ->
              first [ (function Node | Constr -> true | _ -> false) ]
          | None -> (
              match
                first
                  [
                    (function Fn | Rule | Prim | Oracle -> true | _ -> false);
                    (function Operator -> true | _ -> false);
                    (function Type _ -> true | _ -> false);
                  ]
              with
              | [] -> (
                  (* a rule: of the function around [o], else of any *)
                  let around =
                    match Hashtbl.find_opt index f with
                    | Some (_, ds) ->
                        List.find_map
                          (fun d ->
                            match d.kind with
                            | (Rule | Extend)
                              when fst d.item <= o && o <= snd d.item ->
                                Some d.name
                            | _ -> None)
                          ds
                    | None -> None
                  in
                  match Option.map rules around with
                  | Some (_ :: _ as l) -> l
                  | _ ->
                      List.filter
                        (fun d ->
                          match d.kind with Label _ -> true | _ -> false)
                        defs)
              | l -> l)
        in
        (found, w)

(** The directory where the built-in modules are written, for definitions in
    them to have a file: one per version of their contents. *)
let builtin_dir =
  Filename.concat
    (Filename.get_temp_dir_name ())
    ("kanon-modules-"
    ^ Digest.to_hex
        (Digest.string (String.concat "\000" (List.map snd Builtin.files))))

(** The file of [f], writing it if it is a built-in module. *)
let file_of f =
  match Loader.builtin f with
  | None -> Some f
  | Some name -> (
      let p = Filename.concat builtin_dir name in
      try
        if not (Sys.file_exists p) then (
          if not (Sys.file_exists builtin_dir) then Sys.mkdir builtin_dir 0o755;
          let tmp = Filename.temp_file ~temp_dir:builtin_dir name ".tmp" in
          Out_channel.with_open_bin tmp (fun oc ->
              output_string oc (List.assoc name Builtin.files));
          Sys.rename tmp p);
        Some p
      with Sys_error _ | Not_found -> None)

let location d : Yojson.Safe.t option =
  match (Hashtbl.find_opt index d.file, file_of d.file) with
  | Some (t, _), Some f ->
      Some
        (`Assoc [ ("uri", `String (R.uri_of_path f)); ("range", range t d.sel) ])
  | _ -> None

(** The path of the document of a request. *)
let doc_path params =
  Loader.normalize
    (R.path_of_uri
       (Option.value ~default:""
          (R.to_string (R.member "uri" (R.member "textDocument" params)))))

let doc_position params =
  let f = doc_path params in
  let p = R.member "position" params in
  let line = Option.value ~default:0 (R.to_int (R.member "line" p))
  and character = Option.value ~default:0 (R.to_int (R.member "character" p)) in
  let o =
    match contents f with
    | Some s -> offset (text s) ~line ~character
    | None -> 0
  in
  (f, o)

let definition params : Yojson.Safe.t =
  let f, o = doc_position params in
  match List.filter_map location (fst (resolve f o)) with
  | [] -> `Null
  | l -> `List l

let hover params : Yojson.Safe.t =
  let f, o = doc_position params in
  match resolve f o with
  | d :: _, w ->
      let doc =
        match Hashtbl.find_opt index d.file with
        | Some (t, _) -> (
            match d.kind with
            | Label _ -> None
            | _ -> doc_comment t.s (fst d.item))
        | None -> None
      in
      let header =
        match d.kind with
        | Label g -> "rule " ^ g ^ " =\n  | " ^ d.header
        | _ -> d.header
      in
      let value =
        String.concat "\n\n"
          ((("```kanon\n" ^ header ^ "\n```") :: Option.to_list doc)
          @ [ "*" ^ Loader.source_name d.file ^ "*" ])
      in
      let t = text (Option.value (contents f) ~default:"") in
      `Assoc
        [
          ( "contents",
            `Assoc [ ("kind", `String "markdown"); ("value", `String value) ] );
          ("range", range t w);
        ]
  | [], _ -> `Null

let keywords =
  String.split_on_char ' '
    "rule fn prim oracle extend before node type of infix prefix constant use \
     let in match with if then else when as assert not true false land lor \
     lxor lsl lsr asr"

let completion params : Yojson.Safe.t =
  let f, _ = doc_position params in
  let seen = Hashtbl.create 64 in
  let item label kind detail =
    if Hashtbl.mem seen label then None
    else (
      Hashtbl.add seen label ();
      Some
        (R.obj
           [
             ("label", Some (`String label));
             ("kind", Some (`Int kind));
             ("detail", Option.map (fun d -> `String (one_line d)) detail);
           ]))
  in
  let defs =
    List.filter_map
      (fun d ->
        match d.kind with
        | Fn | Rule | Prim | Oracle -> item d.name 3 (Some d.header)
        | Node | Constr -> item d.name 4 (Some d.header)
        | Type record -> item d.name (if record then 22 else 7) (Some d.header)
        | Operator
          when is_word_char d.name.[0] && not (List.mem d.name keywords) ->
            item d.name 24 (Some d.header)
        | _ -> None)
      (lang_defs f)
  in
  `List (defs @ List.filter_map (fun k -> item k 14 None) keywords)

let symbol_kind = function
  | Fn | Rule | Prim | Oracle -> 12
  | Node | Constr -> 9
  | Type record -> if record then 23 else 5
  | Operator -> 25
  | Label _ -> 22
  | Extend -> 12

let workspace_symbol params : Yojson.Safe.t =
  let q =
    String.lowercase_ascii
      (Option.value ~default:"" (R.to_string (R.member "query" params)))
  in
  let contains s =
    let s = String.lowercase_ascii s and n = String.length q in
    let rec go i =
      i + n <= String.length s && (String.sub s i n = q || go (i + 1))
    in
    go 0
  in
  let files = List.sort compare (Hashtbl.fold (fun f _ l -> f :: l) index []) in
  `List
    (List.concat_map
       (fun f ->
         List.filter_map
           (fun d ->
             let name, container =
               match d.kind with
               | Label g -> (g ^ "/" ^ d.name, Some g)
               | _ -> (d.name, None)
             in
             match (d.kind, location d) with
             | Extend, _ | _, None -> None
             | _, Some loc when contains name ->
                 Some
                   (R.obj
                      [
                        ("name", Some (`String name));
                        ("kind", Some (`Int (symbol_kind d.kind)));
                        ("location", Some loc);
                        ( "containerName",
                          Option.map (fun g -> `String g) container );
                      ])
             | _ -> None)
           (List.concat_map flat (snd (Hashtbl.find index f))))
       files)

let document_symbol params : Yojson.Safe.t =
  match Hashtbl.find_opt index (doc_path params) with
  | None -> `List []
  | Some (t, defs) ->
      let rec symbol d : Yojson.Safe.t =
        `Assoc
          [
            ( "name",
              `String
                (match d.kind with Extend -> "extend " ^ d.name | _ -> d.name)
            );
            ("detail", `String (one_line d.header));
            ("kind", `Int (symbol_kind d.kind));
            ("range", range t d.item);
            ("selectionRange", range t d.sel);
            ("children", `List (List.map symbol d.children));
          ]
      in
      `List (List.map symbol defs)

(** {1 The server} *)

let shutdown = ref false

let capabilities : Yojson.Safe.t =
  `Assoc
    [
      ( "capabilities",
        `Assoc
          [
            ( "textDocumentSync",
              `Assoc
                [
                  ("openClose", `Bool true);
                  ("change", `Int 1);
                  ("save", `Assoc [ ("includeText", `Bool false) ]);
                ] );
            ("definitionProvider", `Bool true);
            ("hoverProvider", `Bool true);
            ("completionProvider", `Assoc []);
            ("workspaceSymbolProvider", `Bool true);
            ("documentSymbolProvider", `Bool true);
          ] );
      ("serverInfo", `Assoc [ ("name", `String "kanon") ]);
    ]

let initialize params =
  let uris =
    match R.to_list (R.member "workspaceFolders" params) with
    | [] -> Option.to_list (R.to_string (R.member "rootUri" params))
    | l -> List.filter_map (fun w -> R.to_string (R.member "uri" w)) l
  in
  let paths =
    match uris with
    | [] -> Option.to_list (R.to_string (R.member "rootPath" params))
    | l -> List.map R.path_of_uri l
  in
  folders :=
    List.map
      (fun p ->
        Loader.normalize
          (if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p
           else p))
      paths;
  rescan ();
  capabilities

let notification meth params =
  match meth with
  | _
    when String.starts_with ~prefix:"textDocument/" meth
         && String.starts_with ~prefix:builtin_dir (doc_path params) ->
      (* a built-in module, opened from a definition, is not checked *)
      ()
  | "textDocument/didOpen" ->
      let f = doc_path params in
      Option.iter
        (fun s -> Hashtbl.replace docs f s)
        (R.to_string (R.member "text" (R.member "textDocument" params)));
      if
        not
          (List.exists
             (fun d -> String.starts_with ~prefix:(d ^ "/") f)
             !folders)
      then folders := !folders @ [ Filename.dirname f ];
      rescan ();
      dirty := f :: !dirty
  | "textDocument/didChange" ->
      let f = doc_path params in
      (match List.rev (R.to_list (R.member "contentChanges" params)) with
      | c :: _ ->
          Option.iter
            (fun s -> Hashtbl.replace docs f s)
            (R.to_string (R.member "text" c))
      | [] -> ());
      Hashtbl.replace graph f (scan_uses f);
      dirty := f :: !dirty
  | "textDocument/didSave" ->
      rescan ();
      dirty := doc_path params :: !dirty
  | "textDocument/didClose" ->
      let f = doc_path params in
      Hashtbl.remove docs f;
      Hashtbl.replace graph f (scan_uses f);
      dirty := f :: !dirty
  | "exit" -> exit (if !shutdown then 0 else 1)
  | _ -> ()

let request meth params : Yojson.Safe.t option =
  check ();
  match meth with
  | "initialize" -> Some (initialize params)
  | "shutdown" ->
      shutdown := true;
      Some `Null
  | "textDocument/definition" -> Some (definition params)
  | "textDocument/hover" -> Some (hover params)
  | "textDocument/completion" -> Some (completion params)
  | "workspace/symbol" -> Some (workspace_symbol params)
  | "textDocument/documentSymbol" -> Some (document_symbol params)
  | _ -> None

let handle msg =
  let meth = Option.value ~default:"" (R.to_string (R.member "method" msg)) in
  let params = R.member "params" msg in
  match R.member "id" msg with
  | _ when meth = "" ->
      () (* a response to the server, which sends no request *)
  | `Null -> (
      try notification meth params
      with e -> R.log "kanon lsp: %s: %s" meth (Printexc.to_string e))
  | id -> (
      match request meth params with
      | Some result -> R.respond id result
      | None -> R.respond_error id (-32601) ("unknown method " ^ meth)
      | exception e ->
          R.respond_error id (-32603)
            ("kanon: internal error: " ^ Printexc.to_string e))

(** Serves the messages of standard input, checking the changed files once no
    more messages are waiting, so that a burst of changes is checked once. *)
let run () =
  let rec loop () =
    match R.read () with
    | None -> exit (if !shutdown then 0 else 1)
    | Some msg ->
        handle msg;
        (if not (R.ready ()) then
           try check ()
           with e -> R.log "kanon lsp: check: %s" (Printexc.to_string e));
        loop ()
  in
  loop ()
