(** The language server of Kanon, [kanon lsp]: it checks the languages of the
    open files as they are edited, reports their errors, and answers definition,
    hover, references, highlight, rename, completion and symbol requests from
    the parse trees of the last check.

    A [.kn] file is only meaningful in its language, so the server finds the
    {e roots} of the workspace, the [.knl] files that no other file uses (e.g.
    [lang.knl]), and checks a file as part of each root whose modules contain
    it, as [kanon ocaml root.knl] would. The files of the workspace are found
    once, when its folders are added, and then from the changes that the editor
    reports. The names of a file, local or global, are those of {!Lsp_scope}. *)

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

(** The operator token at the offset [o] of [s], or just before it, if any: its
    span, and the operator as parsed with its arity. A [-] is the prefix [-]
    after an operator, an opening bracket, a separator or a keyword, or at the
    start, and otherwise the infix [-]. This reads the text itself, for a text
    that the last check did not parse; [words] are the infix words of its
    language. *)
let operator_token_at ~words s o =
  let lb = Lexing.from_string s in
  let rec tokens prev acc =
    match Kanon_lexer.token lb with
    | Kanon_parser.EOF -> List.rev acc
    | tok ->
        let a = lb.lex_start_p.pos_cnum and b = lb.lex_curr_p.pos_cnum in
        if a > o + 1 then List.rev acc
        else tokens (Some tok) ((tok, prev, (a, b)) :: acc)
    | exception _ -> List.rev acc
  in
  let toks = tokens None [] in
  let operator (tok, prev, span) =
    let open Kanon_parser in
    let infix s = Some (span, s, 2) and prefix s = Some (span, s, 1) in
    let after_operand =
      match prev with
      | Some
          ( LID _ | UID _ | INT _ | STRING _ | RPAREN | RBRACKET | RBRACE
          | UNDERSCORE | TRUE | FALSE ) ->
          true
      | _ -> false
    in
    match tok with
    | PLUS -> infix "+"
    | MINUS -> if after_operand then infix "-" else prefix "~-"
    | STAR -> infix "*"
    | ANDAND -> infix "&&"
    | BARBAR -> infix "||"
    | CMPOP s | CONCATOP s | ADDOP s | MULOP s | POWOP s -> infix s
    | PREFIXOP s -> prefix s
    | NOT -> prefix "not"
    | INFIXWORD w -> infix w
    | LID w when List.mem w words && after_operand -> infix w
    | _ -> None
  in
  let at p =
    List.find_map
      (fun ((_, _, (a, b)) as t) -> if p a b then operator t else None)
      toks
  in
  match at (fun a b -> a <= o && o < b) with
  | Some _ as r -> r
  | None -> at (fun _ b -> b = o)

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

(** {1 Projects} *)

(** The folders of the workspace. *)
let folders : string list ref = ref []

(** The [.kn] and [.knl] files of the workspace on disk, from a walk of its
    folders when they are added, kept up to date by the changes that the editor
    reports. *)
let files : (string, unit) Hashtbl.t = Hashtbl.create 64

let in_folders f =
  List.exists (fun d -> String.starts_with ~prefix:(d ^ "/") f) !folders

(** Whether [f] exists: an open document, a file of the workspace, or a file
    outside of the workspace on disk. *)
let exists f =
  Hashtbl.mem docs f
  || Hashtbl.mem files f
  || ((not (Filename.is_relative f))
     && (not (in_folders f))
     && Sys.file_exists f)

(** The files that each file may use, existing or not, from a scan of its
    [use]s, computed when needed. *)
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

(** Whether [f] is the source of a built-in module: [modules/bool.kn]. *)
let is_builtin_source f =
  Filename.basename (Filename.dirname f) = "modules"
  && List.mem_assoc (Filename.basename f) Builtin.files

let update_builtin_sources () =
  let before = Hashtbl.copy builtin_sources in
  Hashtbl.reset builtin_sources;
  Hashtbl.iter
    (fun f () ->
      if is_builtin_source f then
        Hashtbl.replace builtin_sources ("+" ^ Filename.basename f) f)
    files;
  (* the uses of the built-in modules then stand for other files *)
  if
    List.sort compare (Hashtbl.fold (fun k v l -> (k, v) :: l) before [])
    <> List.sort compare
         (Hashtbl.fold (fun k v l -> (k, v) :: l) builtin_sources [])
  then Hashtbl.reset graph

(** The modules that [f] uses, from its tokens (without parsing it, which needs
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
          List.map resolve (snd (Loader.module_files (Filename.dirname f) m)))
        (go [])

(** The files that [f] uses. *)
let edges f =
  let l =
    match Hashtbl.find_opt graph f with
    | Some l -> l
    | None ->
        let l = scan_uses f in
        Hashtbl.replace graph f l;
        l
  in
  List.filter exists l

(** [f] changed: its uses are scanned again when needed. *)
let update_file f = Hashtbl.remove graph f

(** Whether [f] is on disk, for the files that the editor creates or deletes. *)
let note_file f =
  if is_kanon f && not (Filename.is_relative f) then (
    if Sys.file_exists f then Hashtbl.replace files f ()
    else Hashtbl.remove files f;
    if is_builtin_source f then update_builtin_sources ())

let add_folder d =
  if not (List.mem d !folders) then (
    folders := !folders @ [ d ];
    List.iter (fun f -> Hashtbl.replace files f ()) (walk d []);
    update_builtin_sources ())

let remove_folder d =
  folders := List.filter (( <> ) d) !folders;
  Hashtbl.filter_map_inplace
    (fun f () ->
      if String.starts_with ~prefix:(d ^ "/") f && not (in_folders f) then None
      else Some ())
    files;
  update_builtin_sources ();
  Hashtbl.reset graph

(** All the files known: those of the workspace and the open documents. *)
let all_files () =
  List.sort_uniq compare
    (Hashtbl.fold (fun f () l -> f :: l) files []
    @ Hashtbl.fold (fun f _ l -> f :: l) docs [])

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

(** The files that use [f], or would if it existed. *)
let users f =
  List.filter
    (fun g ->
      ignore (edges g);
      List.mem f (Option.value (Hashtbl.find_opt graph g) ~default:[]))
    (all_files ())

(** The [.knl] files that no other file uses. *)
let roots () =
  let all = all_files () in
  let used = Hashtbl.create 64 in
  List.iter
    (fun f -> List.iter (fun g -> Hashtbl.replace used g ()) (edges f))
    all;
  List.filter
    (fun f -> Filename.check_suffix f ".knl" && not (Hashtbl.mem used f))
    all

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
  | Operator of int  (** its arity *)
  | Label of string  (** a rule of the function *)
  | Extend  (** [extend rule f], whose rules are its children *)

(** What else a definition says, for the analysis of names and the hovers. *)
type info =
  | No_info
  | Constr_info of {
      args : string list;  (** the types of its arguments *)
      sorts : string list;  (** the sorts of its typing *)
      laws : (string * string * span) list;
          (** its laws: their names, arguments and attributes *)
    }
  | Rule_info of string option  (** the node of its spec *)
  | Op_info of { node : string; smart : string; value : string option }
  | Law_info  (** a rule derived from a law, at the law *)

and span = int * int

type def = {
  name : string;
  kind : kind;
  file : string;
  sel : span;  (** the span of its name *)
  item : span;  (** the span of the item *)
  header : string;  (** its source, or that of its header *)
  children : def list;  (** the rules of a rule, the constructors of a type *)
  info : info;
}

(** The last parse of a file: its text, its definitions and its parse tree. *)
type entry = { text : text; defs : def list; str : Ppxlib.structure }

(** The last parse of each file, from the checks. *)
let index : (string, entry) Hashtbl.t = Hashtbl.create 64

(** Whether the last parse of [f] is that of its contents. *)
let fresh f =
  match (Hashtbl.find_opt index f, contents f) with
  | Some e, Some s -> e.text.s = s
  | _ -> false

let rec flat d = d :: List.concat_map flat d.children
let span = Lsp_scope.span

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

let attr_string_loc name (attrs : Ppxlib.attributes) =
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
                    ( {
                        pexp_desc = Pexp_constant (Pconst_string (s, _, _));
                        pexp_loc;
                        _;
                      },
                      _ );
                _;
              };
            ] ->
            Some (s, pexp_loc)
        | _ -> None)
    attrs

let attr_string name attrs = Option.map fst (attr_string_loc name attrs)

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
                  info = No_info;
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

(** The laws of the operators: the attributes that declare them. *)
let law_attrs = [ "fold"; "unit"; "zero"; "idem"; "invol" ]

(** What the declaration of the constructor [cd] says. *)
let constr_info s (cd : Ppxlib.constructor_declaration) =
  let args =
    match cd.pcd_args with
    | Pcstr_tuple l ->
        List.map (fun (t : Ppxlib.core_type) -> sub s (span t.ptyp_loc)) l
    | Pcstr_record _ -> []
  in
  let sorts =
    List.concat_map
      (fun (a : Ppxlib.attribute) ->
        match a.attr_payload with
        | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ]
          when a.attr_name.txt = "sorts" -> (
            match e.pexp_desc with
            | Pexp_tuple l ->
                List.map
                  (fun (e : Ppxlib.expression) -> sub s (span e.pexp_loc))
                  l
            | _ -> [ sub s (span e.pexp_loc) ])
        | _ -> [])
      cd.pcd_attributes
  in
  let laws =
    List.filter_map
      (fun (a : Ppxlib.attribute) ->
        if List.mem a.attr_name.txt law_attrs then
          let arg =
            match a.attr_payload with
            | PStr
                [
                  {
                    pstr_desc =
                      Pstr_eval
                        ( {
                            pexp_desc = Pexp_constant (Pconst_string (c, _, _));
                            _;
                          },
                          _ );
                    _;
                  };
                ] ->
                c
            | _ -> ""
          in
          Some (a.attr_name.txt, arg, span a.attr_loc)
        else None)
      cd.pcd_attributes
  in
  Constr_info { args; sorts; laws }

(** The definitions of the items [str] of the file [file], of text [s]. *)
let defs_of file s (str : Ppxlib.structure) =
  List.concat_map
    (fun (si : Ppxlib.structure_item) ->
      let item = span si.pstr_loc in
      let mk ?(children = []) ?(header = clip 10 (String.trim (sub s item)))
          ?(info = No_info) name kind sel =
        { name; kind; file; sel; item; header; children; info }
      in
      match si.pstr_desc with
      | Pstr_value
          ( _,
            [
              {
                pvb_pat = { ppat_desc = Ppat_var { txt = x; loc }; _ };
                pvb_attributes;
                pvb_expr;
                _;
              };
            ] ) -> (
          match
            List.find_map
              (fun (a : Ppxlib.attribute) ->
                match a.attr_payload with
                | PStr [ { pstr_desc = Pstr_eval (e, _); _ } ]
                  when a.attr_name.txt = "spec" ->
                    Some e
                | _ -> None)
              pvb_attributes
          with
          | Some spec ->
              let node =
                match spec.pexp_desc with
                | Pexp_construct ({ txt = Lident n; _ }, _) -> Some n
                | _ -> None
              in
              [
                mk ~header:(header s item)
                  ~children:(labels file s x (rule_cases pvb_expr))
                  ~info:(Rule_info node) x Rule (span loc);
              ]
          | None -> [ mk ~header:(header s item) x Fn (span loc) ])
      | Pstr_primitive vd ->
          let x = vd.pval_name.txt in
          [
            mk x
              (if vd.pval_prim = [ "oracle" ] then Oracle else Prim)
              (span vd.pval_name.loc);
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
          [
            mk ~info:(constr_info s cd) cd.pcd_name.txt Node
              (span cd.pcd_name.loc);
          ]
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
              info = constr_info s cd;
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
            ( attr_string_loc "infix" attrs,
              attr_string_loc "prefix" attrs,
              attr_string_loc "extend" attrs,
              e.pexp_desc )
          with
          | Some (op, loc), _, _, _ | None, Some (op, loc), _, _ ->
              let text (e : Ppxlib.expression) = sub s (span e.pexp_loc) in
              let info =
                match e.pexp_desc with
                | Pexp_tuple (n :: sm :: v) ->
                    Op_info
                      {
                        node = text n;
                        smart = text sm;
                        value = Option.map text (List.nth_opt v 0);
                      }
                | _ -> No_info
              in
              let arity = if attr_string "infix" attrs = None then 1 else 2 in
              [ mk ~info op (Operator arity) (span loc) ]
          | ( None,
              None,
              Some (f, loc),
              Pexp_function (_, _, Pfunction_cases (cs, _, _)) ) ->
              [
                mk ~header:(header s item) ~children:(labels file s f cs) f
                  Extend (span loc);
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

(** The errors of the files [u], as [kanon] would check them, and the files it
    parses, with their parse trees. As many errors as can be found independently
    are reported (see {!Check.program_errors}). *)
let errors_of_unit ~read u =
  let parsed = ref [] in
  Check.reset ();
  let errors =
    try
      let langs, rules =
        Loader.load ~read ~resolve
          ~on_parse:(fun f str -> parsed := (f, str) :: !parsed)
          u
      in
      if langs = [] then []
      else
        match Check.language_errors (List.concat_map snd langs) with
        | [] when rules <> [] ->
            Check.program_errors (List.concat_map snd rules)
        | errors -> errors
    with
    | Check.Error (loc, msg) | Loader.Missing (loc, msg) -> [ (loc, msg) ]
    | e ->
        [
          ( Ppxlib.Location.none,
            "kanon: internal error: " ^ Printexc.to_string e );
        ]
  in
  (errors, List.rev !parsed)

(** Checks the unit [u], as [kanon] does, and indexes the files it parses. *)
let check_unit u =
  let main = List.hd u in
  let texts = Hashtbl.create 16 in
  let text_of f =
    match Hashtbl.find_opt texts f with
    | Some t -> t
    | None ->
        let t = Option.map text (contents f) in
        Hashtbl.add texts f t;
        t
  in
  let read f = Option.map (fun t -> t.s) (text_of f) in
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
  let t0 = Unix.gettimeofday () in
  let errors, parsed = errors_of_unit ~read u in
  R.log "kanon lsp: checked %s in %.0fms" (String.concat " " u)
    ((Unix.gettimeofday () -. t0) *. 1000.);
  List.iter
    (fun (f, str) ->
      match text_of f with
      | Some t ->
          Hashtbl.replace index f { text = t; defs = defs_of f t.s str; str }
      | None -> ())
    parsed;
  let diags = List.map (fun (loc, msg) -> diag loc msg) errors in
  let files =
    List.sort_uniq compare (closure u @ List.map fst parsed @ List.map fst diags)
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
    (* an error found through several roots is reported once *)
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
    (* the units that are no longer units, e.g. a root that is now used, or a
       file that was deleted *)
    Hashtbl.filter_map_inplace
      (fun u (fs, ds) ->
        if
          List.for_all exists u
          && List.mem u (units_of (List.nth u (List.length u - 1)))
        then Some (fs, ds)
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
      (List.sort_uniq compare
         (List.concat_map units_of (List.filter exists changed)));
    List.iter publish (List.sort_uniq compare (changed @ !affected)))

(** {1 Names} *)

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
      | Some e -> List.concat_map flat e.defs
      | None -> [])
    (lang_files f)

(** A language, for the analysis of the names of its files. *)
type lang = {
  files : string list;
  defs : def list;
  occs : (string, Lsp_scope.occ list) Hashtbl.t;
      (** the occurrences of the names of each file, once computed *)
}

let lang_of f =
  { files = lang_files f; defs = lang_defs f; occs = Hashtbl.create 8 }

let find_defs lang p = List.filter p lang.defs

(** The context of the analysis of the file [file] of [lang]. *)
let rec scope_ctx lang file (e : entry) : Lsp_scope.ctx =
  let values = Hashtbl.create 64 and nodes = Hashtbl.create 64 in
  List.iter
    (fun d ->
      match d.kind with
      | Fn | Rule | Prim | Oracle -> Hashtbl.replace values d.name ()
      | Node -> Hashtbl.replace nodes d.name ()
      | _ -> ())
    lang.defs;
  {
    file;
    src = e.text.s;
    is_global = Hashtbl.mem values;
    is_node = Hashtbl.mem nodes;
    node_sig =
      (fun c ->
        List.find_map
          (fun d ->
            match (d.kind, d.info) with
            | (Node | Constr), Constr_info { args; sorts; _ } when d.name = c ->
                Some (args, sorts)
            | _ -> None)
          lang.defs);
    fn_params =
      (fun f ->
        match
          List.find_opt
            (fun d -> d.name = f && (d.kind = Rule || d.kind = Fn))
            lang.defs
        with
        | Some d -> (
            match Hashtbl.find_opt index d.file with
            | Some e' ->
                Lsp_scope.fn_binders (scope_ctx lang d.file e') e'.str f
            | None -> [])
        | None -> []);
  }

(** The occurrences of the names of the file [f], from its last parse. *)
let occurrences lang f =
  match Hashtbl.find_opt lang.occs f with
  | Some l -> l
  | None ->
      let l =
        match Hashtbl.find_opt index f with
        | Some e -> Lsp_scope.analyze (scope_ctx lang f e) e.str
        | None -> []
      in
      Hashtbl.replace lang.occs f l;
      l

(** The rule [r] of the function [f] that a law of the node of its spec derives:
    a definition at the attribute of the law (see [Check.law_cases]). *)
let derived_rule lang f r =
  let node =
    List.find_map
      (fun d ->
        match (d.kind, d.info) with
        | Rule, Rule_info (Some n) when d.name = f -> Some n
        | _ -> None)
      lang.defs
  in
  let node_def n =
    List.find_opt
      (fun d -> d.name = n && (d.kind = Node || d.kind = Constr))
      lang.defs
  in
  match Option.bind node node_def with
  | None -> []
  | Some nd -> (
      let laws, sorts =
        match nd.info with
        | Constr_info { laws; sorts; _ } -> (laws, sorts)
        | _ -> ([], [])
      in
      let text sp =
        match Hashtbl.find_opt index nd.file with
        | Some e -> sub e.text.s sp
        | None -> ""
      in
      (* the names of the rules that a law derives (see [Check.law_cases]) *)
      let rule_of (law, arg, _) =
        match law with
        | "fold" -> (
            match List.length sorts with
            | 2 -> [ "lit" ]
            | 3 -> [ "lits" ]
            | _ -> [ "lit"; "lits" ])
        | "unit" | "zero" -> (
            match arg with
            | "0" -> [ "zero" ]
            | "1" -> [ "one" ]
            | c -> [ c ^ "_" ])
        | "idem" -> [ "same" ]
        | "invol" -> [ String.lowercase_ascii nd.name ]
        | _ -> []
      in
      match List.find_opt (fun l -> List.mem r (rule_of l)) laws with
      | Some (_, _, sp) ->
          [
            {
              name = r;
              kind = Label f;
              file = nd.file;
              sel = sp;
              item = sp;
              header =
                Printf.sprintf "%s: (* derived from %s, of %s *)" r (text sp)
                  nd.name;
              children = [];
              info = Law_info;
            };
          ]
      | None -> [])

(** The definitions of the global name [g]. *)
let global_defs lang (g : Lsp_scope.global) =
  match g with
  | Value x ->
      find_defs lang (fun d ->
          d.name = x
          && match d.kind with Fn | Rule | Prim | Oracle -> true | _ -> false)
  | Constr c ->
      let l = find_defs lang (fun d -> d.name = c && d.kind = Node) in
      if l <> [] then l
      else find_defs lang (fun d -> d.name = c && d.kind = Constr)
  | Type t ->
      find_defs lang (fun d ->
          d.name = t && match d.kind with Type _ -> true | _ -> false)
  | Op (sym, arity) ->
      find_defs lang (fun d ->
          d.name = Lsp_scope.written_sym sym && d.kind = Operator arity)
  | Label (f, r) -> (
      match find_defs lang (fun d -> d.name = r && d.kind = Label f) with
      | [] -> derived_rule lang f r
      | l -> l)

(** The global name that a definition defines. *)
let global_of_def d : Lsp_scope.global option =
  match d.kind with
  | Fn | Rule | Prim | Oracle -> Some (Value d.name)
  | Node | Constr -> Some (Constr d.name)
  | Type _ -> Some (Type d.name)
  | Operator arity ->
      Some (Op (Lsp_scope.parsed_sym ~prefix:(arity = 1) d.name, arity))
  | Label f -> Some (Label (f, d.name))
  | Extend -> Some (Value d.name)

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

(** The definitions of the word at the offset [o] of the file [f], and its span,
    by name: for a text that the last check did not parse. *)
let resolve_word lang f o =
  match contents f with
  | None -> ([], (0, 0))
  | Some s -> (
      let words =
        List.filter_map
          (fun d ->
            if d.kind = Operator 2 && Lsp_scope.is_word d.name then Some d.name
            else None)
          lang.defs
      in
      match operator_token_at ~words s o with
      | Some (sp, sym, arity) -> (global_defs lang (Op (sym, arity)), sp)
      | None ->
          let w = word_at s o in
          let x = sub s w in
          if x = "" then ([], w)
          else
            let defs = List.filter (fun d -> d.name = x) lang.defs in
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
                        (function
                        | Fn | Rule | Prim | Oracle -> true
                        | _ -> false);
                        (function Operator _ -> true | _ -> false);
                        (function Type _ -> true | _ -> false);
                      ]
                  with
                  | [] -> (
                      (* a rule: of the function around [o], else of any *)
                      let around =
                        match Hashtbl.find_opt index f with
                        | Some e ->
                            List.find_map
                              (fun d ->
                                match d.kind with
                                | (Rule | Extend)
                                  when fst d.item <= o && o <= snd d.item ->
                                    Some d.name
                                | _ -> None)
                              e.defs
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
            (found, w))

(** What is at the offset [o] of the file [f]. *)
type at =
  | At_local of Lsp_scope.binder * Lsp_scope.occ
  | At_global of Lsp_scope.global option * def list * Lsp_scope.occ option
      (** the name, if known, and its definitions *)

(** The occurrence of a name at the offset [o] of the file [f], if the last
    parse of [f] is that of its contents: the one around [o], else the one that
    ends at [o]. *)
let occurrence_at lang f o =
  if not (fresh f) then None
  else
    let occs = occurrences lang f in
    match
      List.find_opt
        (fun (oc : Lsp_scope.occ) -> fst oc.span <= o && o < snd oc.span)
        occs
    with
    | Some oc -> Some oc
    | None -> List.find_opt (fun (oc : Lsp_scope.occ) -> snd oc.span = o) occs

(** What is at the offset [o] of [f], and its span. *)
let at lang f o =
  match occurrence_at lang f o with
  | Some ({ target = Local b; _ } as oc) -> Some (At_local (b, oc), oc.span)
  | Some ({ target = Global g; _ } as oc) ->
      Some (At_global (Some g, global_defs lang g, Some oc), oc.span)
  | None -> (
      match resolve_word lang f o with
      | [], _ -> None
      | (d :: _ as defs), sp ->
          Some (At_global (global_of_def d, defs, None), sp))

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

(** The location of the span [sp] of the file [file], from its last parse. *)
let location_of file sp : Yojson.Safe.t option =
  match (Hashtbl.find_opt index file, file_of file) with
  | Some e, Some f ->
      Some
        (`Assoc
           [ ("uri", `String (R.uri_of_path f)); ("range", range e.text sp) ])
  | _ -> None

let location d = location_of d.file d.sel

(** {1 Requests} *)

(** A request that fails, with its message. *)
exception Failed of string

let failed fmt = Printf.ksprintf (fun s -> raise (Failed s)) fmt

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
  let lang = lang_of f in
  match at lang f o with
  | Some (At_local (b, _), _) -> (
      match location_of b.file b.span with
      | Some l -> `List [ l ]
      | None -> `Null)
  | Some (At_global (_, defs, _), _) -> (
      match List.filter_map location defs with [] -> `Null | l -> `List l)
  | None -> `Null

(** The line of the offset [o] of [file], from 1. *)
let line_number file o =
  match Hashtbl.find_opt index file with
  | Some e -> line_of e.text o + 1
  | None -> 0

let markdown ?range:r f value : Yojson.Safe.t =
  let t = text (Option.value (contents f) ~default:"") in
  R.obj
    [
      ( "contents",
        Some (`Assoc [ ("kind", `String "markdown"); ("value", `String value) ])
      );
      ("range", Option.map (range t) r);
    ]

let local_hover f (b : Lsp_scope.binder) =
  let what =
    match b.kind with
    | Param "" -> "Parameter"
    | Param g -> Printf.sprintf "Parameter of `%s`" g
    | Spec_operand (g, c) ->
        Printf.sprintf
          "Parameter of the rule `%s`: an operand of its spec, `%s`" g c
    | Pattern_var -> "Pattern variable"
    | Literal_var -> "Pattern variable, the value of a literal (`#x`)"
    | Let_var -> "Variable bound by `let`"
    | Let_fn -> "Local function"
    | Sort_var w -> "Variable of a sort, bound by " ^ w
    | Node_param c ->
        Printf.sprintf "Argument of the node `%s`, in its typing" c
    | Constant_param c ->
        Printf.sprintf "The term at whose sort `constant \"%s\"` is built" c
  in
  let code =
    match (b.kind, b.ty) with
    | Let_fn, Some h -> h
    | _, Some t -> b.name ^ " : " ^ t
    | _, None -> b.name
  in
  let where =
    Printf.sprintf "Bound on line %d%s."
      (line_number b.file (fst b.span))
      (if b.file = f then "" else " of *" ^ Loader.source_name b.file ^ "*")
  in
  String.concat "\n\n"
    ([ "```kanon\n" ^ code ^ "\n```"; what ^ ". " ^ where ]
    @ Option.to_list
        (Option.map (fun n -> String.capitalize_ascii n ^ ".") b.note))

(** What an operator builds and matches, from its declaration [d]. *)
let operator_text d (oc : Lsp_scope.occ option) =
  match (d.kind, d.info) with
  | Operator arity, Op_info { node; smart; value } ->
      let use = if arity = 1 then d.name ^ "a" else "a " ^ d.name ^ " b" in
      let use =
        if arity = 1 && Lsp_scope.is_word d.name then d.name ^ " a" else use
      in
      let args = if arity = 1 then "a" else "a b" in
      let in_pattern =
        match oc with Some { in_pattern = true; _ } -> true | _ -> false
      in
      [
        (if in_pattern then
           Printf.sprintf "In this pattern, `%s` matches the node `%s`." use
             node
         else
           Printf.sprintf
             "`%s` is `%s %s` on terms; in patterns, it matches the node `%s`."
             use smart args node);
      ]
      @ Option.to_list
          (Option.map
             (fun v ->
               Printf.sprintf "On the values of literals, it is `%s`." v)
             value)
  | _ -> []

let hover params : Yojson.Safe.t =
  let f, o = doc_position params in
  let lang = lang_of f in
  match at lang f o with
  | Some (At_local (b, _), sp) -> markdown ~range:sp f (local_hover f b)
  | Some (At_global (_, d :: _, oc), sp) ->
      let doc =
        match Hashtbl.find_opt index d.file with
        | Some e -> (
            match d.kind with
            | Label _ -> None
            | _ -> doc_comment e.text.s (fst d.item))
        | None -> None
      in
      let header =
        match d.kind with
        | Label g -> "rule " ^ g ^ " =\n  | " ^ d.header
        | _ -> d.header
      in
      let value =
        String.concat "\n\n"
          ((("```kanon\n" ^ header ^ "\n```") :: operator_text d oc)
          @ Option.to_list doc
          @ [ "*" ^ Loader.source_name d.file ^ "*" ])
      in
      markdown ~range:sp f value
  | _ -> `Null

(** {2 References} *)

let same_target (a : Lsp_scope.target) (b : Lsp_scope.target) =
  match (a, b) with
  | Local x, Local y -> x.file = y.file && x.span = y.span
  | Global g, Global h -> g = h
  | _ -> false

(** The target of what is at the offset [o] of [f], and its span. *)
let target_at lang f o : (Lsp_scope.target * span) option =
  match at lang f o with
  | Some (At_local (b, _), sp) -> Some (Local b, sp)
  | Some (At_global (Some g, _, _), sp) -> Some (Global g, sp)
  | _ -> None

(** The occurrences of [t] in the files of [lang]: file, span, and whether it is
    a definition. *)
let references lang (t : Lsp_scope.target) =
  let files =
    match t with
    | Local b when not (List.mem b.file lang.files) -> [ b.file ]
    | _ -> lang.files
  in
  List.concat_map
    (fun file ->
      List.filter_map
        (fun (oc : Lsp_scope.occ) ->
          if same_target oc.target t then Some (file, oc.span, oc.decl)
          else None)
        (occurrences lang file))
    files
  |> List.sort_uniq compare

let references_request params : Yojson.Safe.t =
  let f, o = doc_position params in
  let decl =
    R.member "includeDeclaration" (R.member "context" params) = `Bool true
  in
  let lang = lang_of f in
  match target_at lang f o with
  | None -> `Null
  | Some (t, _) ->
      `List
        (List.filter_map
           (fun (file, sp, d) ->
             if d && not decl then None else location_of file sp)
           (references lang t))

let document_highlight params : Yojson.Safe.t =
  let f, o = doc_position params in
  let lang = lang_of f in
  match (target_at lang f o, Hashtbl.find_opt index f) with
  | Some (t, _), Some e when fresh f ->
      `List
        (List.filter_map
           (fun (file, sp, decl) ->
             if file <> f then None
             else
               Some
                 (`Assoc
                    [
                      ("range", range e.text sp);
                      ("kind", `Int (if decl then 3 else 2));
                    ]))
           (references lang t))
  | _ -> `Null

(** {2 Renaming} *)

let keywords =
  String.split_on_char ' '
    "rule fn prim oracle extend before node sort type of infix prefix constant \
     use let in match with if then else when as assert not true false"

(** What [t] is, to rename it, or why it cannot be renamed. *)
let renamable lang (t : Lsp_scope.target) =
  let in_builtin file =
    match Loader.builtin file with
    | Some name ->
        failed "%s is in the built-in module %s, which cannot be edited"
          (match t with
          | Local b -> b.name
          | Global (Value x | Constr x | Type x | Label (_, x)) -> x
          | Global (Op (s, _)) -> Lsp_scope.written_sym s)
          name
    | None -> ()
  in
  match t with
  | Local b ->
      in_builtin b.file;
      `Lower
  | Global (Op _) -> failed "operators cannot be renamed"
  | Global g -> (
      let defs = global_defs lang g in
      let defs =
        match g with
        | Label (f, _) -> List.filter (fun d -> d.kind = Label f) defs
        | _ -> defs
      in
      match (g, defs) with
      | Type ("t" | "ty"), _ ->
          failed "t and ty are the types of terms, which a language declares"
      | Label (f, r), [] -> failed "%s has no rule %s" f r
      | Label (_, r), defs when List.for_all (fun d -> d.info = Law_info) defs
        ->
          failed "the rule %s is derived from a law" r
      | (Value x | Constr x | Type x), [] -> failed "%s is built into Kanon" x
      | Label (_, x), _ :: _ when List.mem x [ "default" ] ->
          failed "default is the rule that Kanon adds"
      | _, defs ->
          List.iter (fun d -> in_builtin d.file) defs;
          if match g with Constr _ -> true | _ -> false then `Upper
          else `Lower)

(** Checks that [x] can be the new name of [t]. *)
let valid_name lang (t : Lsp_scope.target) case x =
  let ok_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
    | _ -> false
  in
  let well_formed =
    x <> ""
    && String.for_all ok_char x
    &&
    match (case, x.[0]) with
    | `Upper, 'A' .. 'Z' -> true
    | `Lower, ('a' .. 'z' | '_') -> x <> "_"
    | _ -> false
  in
  if not well_formed then
    failed "%s is not a valid name: %s" x
      (match case with
      | `Upper -> "constructors start with an uppercase letter"
      | `Lower -> "names start with a lowercase letter or _");
  if List.mem x keywords then failed "%s is a keyword" x;
  if List.exists (fun d -> d.name = x && d.kind = Operator 2) lang.defs then
    failed "%s is an infix operator of the language" x;
  let taken p = List.exists (fun d -> d.name = x && p d.kind) lang.defs in
  let value = function Fn | Rule | Prim | Oracle -> true | _ -> false in
  match t with
  | Local _ | Global (Value _) ->
      if taken value || x = "type_of" then failed "%s is already a function" x
  | Global (Constr _) ->
      if taken (function Node | Constr -> true | _ -> false) then
        failed "%s is already a constructor" x
  | Global (Type _) ->
      if
        taken (function Type _ -> true | _ -> false)
        || List.mem x Lsp_scope.builtin_types
      then failed "%s is already a type" x
  | Global (Label (f, _)) ->
      if taken (fun k -> k = Label f) then failed "%s already has a rule %s" f x
  | Global (Op _) -> ()

let prepare_rename params : Yojson.Safe.t =
  let f, o = doc_position params in
  let lang = lang_of f in
  match target_at lang f o with
  | None -> failed "nothing to rename here"
  | Some (t, sp) ->
      ignore (renamable lang t);
      let s = Option.value (contents f) ~default:"" in
      `Assoc
        [ ("range", range (text s) sp); ("placeholder", `String (sub s sp)) ]

let rename params : Yojson.Safe.t =
  let f, o = doc_position params in
  let lang = lang_of f in
  let x = Option.value ~default:"" (R.to_string (R.member "newName" params)) in
  match target_at lang f o with
  | None -> failed "nothing to rename here"
  | Some (t, _) ->
      let case = renamable lang t in
      valid_name lang t case x;
      let refs = references lang t in
      let files = List.sort_uniq compare (List.map (fun (f, _, _) -> f) refs) in
      List.iter
        (fun file ->
          if not (fresh file) then
            failed
              "%s has changed since it was last checked (does it have a syntax \
               error?)"
              (Filename.basename file))
        files;
      `Assoc
        [
          ( "changes",
            `Assoc
              (List.filter_map
                 (fun file ->
                   match (Hashtbl.find_opt index file, file_of file) with
                   | Some e, Some path ->
                       Some
                         ( R.uri_of_path path,
                           `List
                             (List.filter_map
                                (fun (g, sp, _) ->
                                  if g <> file then None
                                  else
                                    Some
                                      (`Assoc
                                         [
                                           ("range", range e.text sp);
                                           ("newText", `String x);
                                         ]))
                                refs) )
                   | _ -> None)
                 files) );
        ]

(** {2 Completion and symbols} *)

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
        | Operator _
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
  | Operator _ -> 25
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
           (List.concat_map flat (Hashtbl.find index f).defs))
       files)

let document_symbol params : Yojson.Safe.t =
  match Hashtbl.find_opt index (doc_path params) with
  | None -> `List []
  | Some e ->
      let rec symbol d : Yojson.Safe.t =
        `Assoc
          [
            ( "name",
              `String
                (match d.kind with Extend -> "extend " ^ d.name | _ -> d.name)
            );
            ("detail", `String (one_line d.header));
            ("kind", `Int (symbol_kind d.kind));
            ("range", range e.text d.item);
            ("selectionRange", range e.text d.sel);
            ("children", `List (List.map symbol d.children));
          ]
      in
      `List (List.map symbol e.defs)

(** {1 The server} *)

let shutdown = ref false

(** Whether the client can watch files for the server. *)
let watch_files = ref false

(** The last id of the requests of the server to the client. *)
let request_id = ref 0

(** Sends a request to the client, whose response is ignored. *)
let send_request meth params =
  incr request_id;
  R.send
    (`Assoc
       [
         ("jsonrpc", `String "2.0");
         ("id", `Int !request_id);
         ("method", `String meth);
         ("params", params);
       ])

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
            ("referencesProvider", `Bool true);
            ("documentHighlightProvider", `Bool true);
            ("renameProvider", `Assoc [ ("prepareProvider", `Bool true) ]);
            ("completionProvider", `Assoc []);
            ("workspaceSymbolProvider", `Bool true);
            ("documentSymbolProvider", `Bool true);
            ( "workspace",
              `Assoc
                [
                  ( "workspaceFolders",
                    `Assoc
                      [
                        ("supported", `Bool true);
                        ("changeNotifications", `Bool true);
                      ] );
                ] );
          ] );
      ("serverInfo", `Assoc [ ("name", `String "kanon") ]);
    ]

let folder_path p =
  Loader.normalize
    (if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p)

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
  List.iter (fun p -> add_folder (folder_path p)) paths;
  watch_files :=
    R.member "dynamicRegistration"
      (R.member "didChangeWatchedFiles"
         (R.member "workspace" (R.member "capabilities" params)))
    = `Bool true;
  capabilities

(** [f] changed: it is checked again, with the files that use it. *)
let changed f =
  update_file f;
  dirty := f :: !dirty

let watched_file_changes params =
  List.iter
    (fun c ->
      let f =
        Loader.normalize
          (R.path_of_uri
             (Option.value ~default:"" (R.to_string (R.member "uri" c))))
      in
      if is_kanon f then (
        (match R.to_int (R.member "type" c) with
        | Some 3 -> Hashtbl.remove files f
        | _ -> Hashtbl.replace files f ());
        if is_builtin_source f then update_builtin_sources ();
        if not (Hashtbl.mem docs f) then (
          update_file f;
          (* the files that use [f], or would *)
          dirty := users f @ (f :: !dirty))))
    (R.to_list (R.member "changes" params))

let notification meth params =
  match meth with
  | _
    when String.starts_with ~prefix:"textDocument/" meth
         && String.starts_with ~prefix:builtin_dir (doc_path params) ->
      (* a built-in module, opened from a definition, is not checked *)
      ()
  | "initialized" ->
      if !watch_files then
        send_request "client/registerCapability"
          (`Assoc
             [
               ( "registrations",
                 `List
                   [
                     `Assoc
                       [
                         ("id", `String "kanon-watched-files");
                         ("method", `String "workspace/didChangeWatchedFiles");
                         ( "registerOptions",
                           `Assoc
                             [
                               ( "watchers",
                                 `List
                                   [
                                     `Assoc
                                       [
                                         ("globPattern", `String "**/*.{kn,knl}");
                                       ];
                                   ] );
                             ] );
                       ];
                   ] );
             ])
  | "textDocument/didOpen" ->
      let f = doc_path params in
      Option.iter
        (fun s -> Hashtbl.replace docs f s)
        (R.to_string (R.member "text" (R.member "textDocument" params)));
      if not (in_folders f) then add_folder (Filename.dirname f);
      note_file f;
      changed f
  | "textDocument/didChange" ->
      let f = doc_path params in
      (match List.rev (R.to_list (R.member "contentChanges" params)) with
      | c :: _ ->
          Option.iter
            (fun s -> Hashtbl.replace docs f s)
            (R.to_string (R.member "text" c))
      | [] -> ());
      changed f
  | "textDocument/didSave" ->
      let f = doc_path params in
      note_file f;
      changed f
  | "textDocument/didClose" ->
      let f = doc_path params in
      Hashtbl.remove docs f;
      note_file f;
      changed f
  | "workspace/didChangeWatchedFiles" -> watched_file_changes params
  | "workspace/didChangeWorkspaceFolders" ->
      let event = R.member "event" params in
      let paths k =
        List.filter_map
          (fun w -> Option.map R.path_of_uri (R.to_string (R.member "uri" w)))
          (R.to_list (R.member k event))
      in
      List.iter (fun p -> remove_folder (folder_path p)) (paths "removed");
      List.iter (fun p -> add_folder (folder_path p)) (paths "added");
      dirty := Hashtbl.fold (fun f _ l -> f :: l) docs !dirty
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
  | "textDocument/references" -> Some (references_request params)
  | "textDocument/documentHighlight" -> Some (document_highlight params)
  | "textDocument/prepareRename" -> Some (prepare_rename params)
  | "textDocument/rename" -> Some (rename params)
  | "textDocument/completion" -> Some (completion params)
  | "workspace/symbol" -> Some (workspace_symbol params)
  | "textDocument/documentSymbol" -> Some (document_symbol params)
  | _ -> None

let handle msg =
  let meth = Option.value ~default:"" (R.to_string (R.member "method" msg)) in
  let params = R.member "params" msg in
  match R.member "id" msg with
  | _ when meth = "" -> () (* a response to a request of the server *)
  | `Null -> (
      try notification meth params
      with e -> R.log "kanon lsp: %s: %s" meth (Printexc.to_string e))
  | id -> (
      match request meth params with
      | Some result -> R.respond id result
      | None -> R.respond_error id (-32601) ("unknown method " ^ meth)
      | exception Failed msg -> R.respond_error id (-32803) msg
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
