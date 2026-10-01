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
    rules after theirs.

    [kanon lsp] is the language server of Kanon files (see {!Lsp_server}). *)

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
     \       kanon lsp\n\
      Files use modules with use \"path\", or use +name for those built into \
      kanon: "
    ^ String.concat ", "
        (List.sort_uniq compare
           (List.map
              (fun (n, _) -> "+" ^ Filename.remove_extension n)
              Builtin.files)));
  exit 2

let () =
  match Array.to_list Sys.argv with
  | [ _; "lsp" ] -> Lsp_server.run ()
  | _ :: backend :: files -> (
      try
        if files = [] then usage ();
        let langs, files =
          try Loader.load files with
          | Loader.No_builtin f ->
              Format.eprintf "kanon: %s: no such built-in module file@." f;
              usage ()
          | Loader.Missing (_, msg) ->
              Format.eprintf "kanon: %s@." msg;
              exit 1
        in
        if langs = [] then usage ();
        Check.language (List.concat_map snd langs);
        let prog =
          lazy
            (if files = [] then usage ();
             Check.program (List.concat_map snd files))
        in
        let lang = List.map (fun (f, _) -> Loader.source_name f) langs in
        let sources = List.map (fun (f, _) -> Loader.source_name f) files in
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
