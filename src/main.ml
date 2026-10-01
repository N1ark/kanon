(** [kanon BACKEND FILE...]: generates, from the Kanon rules in the [.kn] files,
    written in the language declared by the [.knl] files (a language and the
    modules it is made of), with the modules that they use, in order:
    - [ocaml]: their OCaml implementation;
    - [ocaml-check]: the OCaml check that the OCaml types of the language agree
      with its declaration (which does not need the rules);
    - [ocaml-tests]: the OCaml differential tests of their rule functions;
    - [lean-types], [lean-syntax]: the Lean definitions of the types of the
      language (which do not need the rules);
    - [lean-signatures]: the Lean check of the types of their primitives;
    - [lean-typing]: the Lean typing predicates of the operators;
    - [lean-model], [lean-statements], [lean-lifts], [lean-soundness]: their
      Lean model, the statements of their soundness, and its proof.

    The output is written on standard output, except for [lean-all], which
    writes every Lean file [F.lean] of the above to [F.lean.gen], in the current
    directory.

    [use "path"], in a file, uses the module whose declarations are [path.knl]
    and whose rules are [path.kn] (either may be missing), relative to the
    directory of the file, and [use +name] the module built into kanon (the
    files of [modules/]). A module is used once, the first time; the
    declarations of a file come before those of the modules it uses, and its
    rules after theirs. *)

(** The generated Lean files, with the backend of each. *)
let lean_files ~lang ~sources prog =
  [
    ("Types", "lean-types", fun ft -> Gen_lean.types ~sources:lang ft);
    ("Syntax", "lean-syntax", fun ft -> Gen_lean.syntax ~sources:lang ft);
    ( "Signatures",
      "lean-signatures",
      fun ft -> Gen_lean.signatures ~sources ft (Lazy.force prog) );
    ( "Typing",
      "lean-typing",
      fun ft -> Gen_lean.typing_file ~sources ft (Lazy.force prog) );
    ( "Model",
      "lean-model",
      fun ft -> Gen_lean.model ~sources ft (Lazy.force prog) );
    ( "Statements",
      "lean-statements",
      fun ft -> Gen_lean.statements ~sources ft (Lazy.force prog) );
    ( "Lifts",
      "lean-lifts",
      fun ft -> Gen_lean.lifts ~sources ft (Lazy.force prog) );
    ( "Soundness",
      "lean-soundness",
      fun ft ->
        Gen_lean.soundness ~sources
          ~proofs:[ Gen_lean.md "Proofs" ]
          ft (Lazy.force prog) );
  ]

let usage () =
  prerr_endline
    ("usage: kanon (ocaml | ocaml-check | ocaml-tests | lean-types | \
      lean-syntax | lean-signatures | lean-typing | lean-model | \
      lean-statements | lean-lifts | lean-soundness | lean-all) FILE...\n\
      Files use modules with use \"path\", or use +name for those built into \
      kanon: "
    ^ String.concat ", "
        (List.sort_uniq compare
           (List.map
              (fun (n, _) -> "+" ^ Filename.remove_extension n)
              Builtin.files)));
  exit 2

(** The name of the built-in module file that [f] names ([+name]), if any. *)
let builtin f =
  if String.starts_with ~prefix:"+" f then
    Some (String.sub f 1 (String.length f - 1))
  else None

let parse_file f =
  match builtin f with
  | None -> Check.parse_file f
  | Some name -> (
      match List.assoc_opt name Builtin.files with
      | Some s -> Check.parse_string ~file:name s
      | None ->
          Format.eprintf "kanon: %s: no such built-in module file@." f;
          usage ())

(** The name of the file [f] in the headers of the generated files. *)
let source_name f = Filename.basename (Option.value (builtin f) ~default:f)

let exists f =
  match builtin f with
  | Some name -> List.mem_assoc name Builtin.files
  | None -> Sys.file_exists f

(** The modules that [items] use, and [items] without their [use]s. *)
let uses (items : Ppxlib.structure) =
  List.partition_map
    (fun (si : Ppxlib.structure_item) ->
      match si.pstr_desc with
      | Pstr_extension
          ( ( { txt = "kanon.use"; _ },
              PStr
                [
                  {
                    pstr_desc =
                      Pstr_eval
                        ( {
                            pexp_desc = Pexp_constant (Pconst_string (m, _, _));
                            _;
                          },
                          _ );
                    _;
                  };
                ] ),
            _ ) ->
          Left m
      | _ -> Right si)
    items

(** The declarations and the rules of [files] and of the modules they use, as
    [(file, items)] lists, in order. *)
let load files =
  let loaded = Hashtbl.create 8 in
  let decls = ref [] and rules = ref [] in
  let rec file f =
    if not (Hashtbl.mem loaded f) then (
      Hashtbl.add loaded f ();
      let ms, items = uses (parse_file f) in
      let is_decl = Filename.check_suffix f ".knl" in
      if is_decl then decls := !decls @ [ (f, items) ];
      List.iter (use (Filename.dirname f)) ms;
      if not is_decl then rules := !rules @ [ (f, items) ])
  and use dir m =
    let base =
      if String.starts_with ~prefix:"+" m || not (Filename.is_relative m) then m
      else Filename.concat dir m
    in
    match List.filter exists [ base ^ ".knl"; base ^ ".kn" ] with
    | [] ->
        Format.eprintf "kanon: use %S: no %s.knl or %s.kn@." m base base;
        exit 1
    | fs -> List.iter file fs
  in
  List.iter file files;
  (!decls, !rules)

let () =
  match Array.to_list Sys.argv with
  | _ :: backend :: files -> (
      try
        if files = [] then usage ();
        let langs, files = load files in
        if langs = [] then usage ();
        Check.language (List.concat_map snd langs);
        let prog =
          lazy
            (if files = [] then usage ();
             Check.program (List.concat_map snd files))
        in
        let lang = List.map (fun (f, _) -> source_name f) langs in
        let sources = List.map (fun (f, _) -> source_name f) files in
        let lean = lean_files ~lang ~sources prog in
        match backend with
        | "ocaml" ->
            Gen_ocaml.program ~sources Format.std_formatter (Lazy.force prog)
        | "ocaml-check" ->
            Gen_ocaml.lang_check ~sources:lang Format.std_formatter
        | "ocaml-tests" ->
            Gen_tests.program ~sources Format.std_formatter (Lazy.force prog)
        | "lean-all" ->
            List.iter
              (fun (name, _, gen) ->
                let oc = open_out_bin (name ^ ".lean.gen") in
                let ft = Format.formatter_of_out_channel oc in
                gen ft;
                Format.pp_print_flush ft ();
                close_out oc)
              lean
        | _ -> (
            match List.find_opt (fun (_, b, _) -> b = backend) lean with
            | Some (_, _, gen) -> gen Format.std_formatter
            | None -> usage ())
      with Check.Error (loc, msg) ->
        Format.eprintf "%a: %s@." Check.pp_loc loc msg;
        exit 1)
  | _ -> usage ()
