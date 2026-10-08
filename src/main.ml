(** [kanon ocaml [--check] DIR FILE...] and [kanon lean [--check] DIR FILE...]
    generate, from the Kanon rules in the [.kn] files, written in the language
    declared by the [.knl] files (a language and the modules it is made of),
    with the modules that they use:
    - [kanon ocaml] writes the OCaml in [DIR/Generated]: the types of the
      language ([types.ml]), the implementation of the rules ([rules.ml]), the
      typed interface of their smart constructors, where terms are typed by the
      tags of their sorts and subsorts ([typed.ml], see {!Gen_typed}), and their
      differential tests ([tests.ml]), after deleting that directory, which
      holds only generated files;
    - [kanon lean] writes the Lean files of each module and of the language in
      the directory [Generated] of [DIR], under its root (as
      [DIR/Generated/R/Model.lean], for the root [R] of a module), after
      deleting the directory [DIR/Generated/R] of each root, which hold only
      generated files: the hand-written files are in [DIR/R].

    With [--check], they only check that those directories are exactly as they
    would be written.

    [use "path"], in a file, uses the module whose declarations are [path.knl]
    and whose rules are [path.kn] (either may be missing), relative to the
    directory of the file, and [use builtin "name"] the module built into kanon
    (the files of [modules/]). A module is used once, the first time; the
    declarations of a file come before those of the modules it uses, and its
    rules after theirs.

    [kanon lsp] is the language server of Kanon files (see {!Lsp_server}), and
    [kanon --version] prints the version of kanon.

    The command line is {!Cli.run}; the web runtime has the parts of the
    generated code apart ({!Parts}). *)

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "lsp" ] -> Lsp_server.run ()
  | args -> exit (Cli.run args Format.std_formatter Format.err_formatter)
