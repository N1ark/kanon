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

    [kanon lsp] is the language server of Kanon files (see {!Lsp_server}).

    The command line is {!Cli.run}. *)

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "lsp" ] -> Lsp_server.run ()
  | args -> exit (Cli.run args Format.std_formatter Format.err_formatter)
