(** The command line of kanon, [kanon BACKEND FILE...] (see {!Main}), as a
    function, for kanon and for its web runtime. *)

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

(** The backends that write on standard output, in the order of the usage. *)
let backends =
  [ "ocaml-types"; "ocaml"; "ocaml-typed"; "ocaml-tests" ]
  @ List.map
      (fun (_, b, _) -> b)
      (lean_files ~lang:[] ~sources:[] (lazy (assert false)))

(** The end of the command, with its exit code. *)
exception Exit_code of int

let usage err =
  Format.fprintf err "%s@."
    ("usage: kanon ("
    ^ String.concat " | " (backends @ [ "lean-all" ])
    ^ ") FILE...\n\
      \       kanon lsp\n\
      \       kanon --version\n\
       Files use modules with use \"path\", or use builtin \"name\" for those \
       built into kanon: "
    ^ String.concat ", "
        (List.sort_uniq compare
           (List.map
              (fun (n, _) -> Printf.sprintf "%S" (Filename.remove_extension n))
              Builtin.files)));
  raise (Exit_code 2)

(** [run args out err] runs [kanon args] (without [lsp]), writing on [out] and
    [err] for standard output and error, and is its exit code. Exceptions other
    than the errors of the files are raised. *)
let run args out err =
  try
    match args with
    | [ "--version" ] ->
        Format.fprintf out "%s@." Version.version;
        0
    | backend :: files -> (
        try
          if files = [] then usage err;
          let langs, files =
            try Loader.load files with
            | Loader.No_builtin f ->
                Format.fprintf err "kanon: %s: no such built-in module file@." f;
                usage err
            | Loader.Missing (_, msg) ->
                Format.fprintf err "kanon: %s@." msg;
                raise (Exit_code 1)
          in
          if langs = [] then usage err;
          Check.language (List.concat_map snd langs);
          let prog =
            lazy
              (if files = [] then usage err;
               Check.program (List.concat_map snd files))
          in
          let lang = List.map (fun (f, _) -> Loader.source_name f) langs in
          let sources = List.map (fun (f, _) -> Loader.source_name f) files in
          let lean = lean_files ~lang ~sources prog in
          (match backend with
          | "ocaml-types" -> Gen_ocaml.types ~sources:lang out
          | "ocaml" -> Gen_ocaml.program ~sources out (Lazy.force prog)
          | "ocaml-typed" ->
              Gen_typed.program ~sources:(lang @ sources) out (Lazy.force prog)
          | "ocaml-tests" -> Gen_tests.program ~sources out (Lazy.force prog)
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
              | Some (_, _, gen) -> gen out
              | None -> usage err));
          0
        with Check.Error (loc, msg) ->
          Format.fprintf err "%a: %s@." Check.pp_loc loc msg;
          1)
    | [] -> usage err
  with Exit_code code -> code
