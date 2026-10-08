(** [kanon BACKEND FILE...]: generates, from the Kanon rules in the [.kn] files,
    written in the language declared by the [.knl] files (a language and the
    modules it is made of), with the modules that they use, in order:
    - [ocaml-types]: the OCaml types of the language, standalone (which do not
      need the rules);
    - [ocaml]: their OCaml implementation, where these types are in scope;
    - [ocaml-typed]: the typed interface of their smart constructors, where
      terms are typed by the tags of their sorts and subsorts (see
      {!Gen_typed}), and its implementation from the rules;
    - [ocaml-tests]: the OCaml differential tests of their rule functions;
    - [lean-types], [lean-node], [lean-lang], [lean-model], [lean-statements],
      [lean-soundness]: the Lean files of each module, under its root: its data
      types, its nodes and sorts, their typing in any language that has them,
      the model of its rules, the statements of their soundness and their
      proofs;
    - [lean-syntax], [lean-semantics], [lean-rules]: the Lean files of the
      language, under its root: its terms, their semantics, and its rule
      functions, put together from those of its modules, with their proof. Each
      backend prints its files one after the other, each after its name.

    The output is written on standard output. [kanon lean-all DIR FILE...]
    writes every Lean file of the above in the directory [Generated] of the
    directory of its root (as [DIR/R/Generated/Model.lean], for the root [R] of
    a module), after deleting those directories, which hold only generated
    files: the hand-written files are beside them, in [DIR/R].
    [kanon ocaml-all DIR FILE...] writes the four OCaml backends in
    [DIR/Generated], the same way. [kanon lean-all --check DIR FILE...] and
    [kanon ocaml-all --check DIR FILE...] only check that those directories are
    exactly as they would be written.

    [use "path"], in a file, uses the module whose declarations are [path.knl]
    and whose rules are [path.kn] (either may be missing), relative to the
    directory of the file, and [use builtin "name"] the module built into kanon
    (the files of [modules/]). A module is used once, the first time; the
    declarations of a file come before those of the modules it uses, and its
    rules after theirs.

    [kanon lsp] is the language server of Kanon files (see {!Lsp_server}), and
    [kanon --version] prints the version of kanon.

    The command line is {!Cli.run}. *)

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "lsp" ] -> Lsp_server.run ()
  | args -> exit (Cli.run args Format.std_formatter Format.err_formatter)
