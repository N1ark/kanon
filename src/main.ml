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
    - [lean-types], [lean-syntax]: the Lean definitions of the types of the
      language (which do not need the rules);
    - [lean-signatures]: the Lean check of the types of their primitives;
    - [lean-typing]: the Lean typing predicates of the operators;
    - [lean-model], [lean-statements], [lean-lifts], [lean-nodes],
      [lean-soundness]: their Lean model, the statements of their soundness, the
      lemmas of the nodes, and its proof, each in several files (one per rule
      function), which are printed one after the other, each after its name.

    The output is written on standard output. [kanon lean-all DIR FILE...]
    writes every Lean file of the above under [DIR] (as [DIR/R/Model.lean], for
    the root [R] of the model), and removes those it wrote before and no longer
    generates; [kanon lean-all --check DIR FILE...] only checks that they are up
    to date.

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
