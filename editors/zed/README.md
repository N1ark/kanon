# Kanon for Zed

A [Zed](https://zed.dev) extension for Kanon, the `.kn` and `.knl` files, with
the grammar of `tree-sitter-kanon/` and the language server of `kanon lsp`:

- the language server (see [below](#language-server)): the errors of the
  checker as you type, in the file and in the other files of the language,
  go to definition, hover with the definition and its comment, completion of
  the names of the language, and project symbol search (`cmd-t`) for rule
  functions, helpers, primitives, nodes, types and the rules of rule
  functions;
- syntax highlighting: keywords, the names of rule functions, helpers and
  primitives where they are defined and called, rule names (`| lit: ...`),
  constructors, types, attributes (`[@comm]`, `[@@@lean_root "R"]`), the
  operators (`&&`, `≤`, and the infix words of patterns such as
  `l urem #n`), `#x` patterns, and nested comments;
- the outline (`cmd-shift-o`, and the outline panel): the items of a file,
  with the rules of each rule function under it (`rule b_and` >
  `false_`, `true_`, ...) and the constructors of each type under it, so
  that a rule can be found by name;
- matching and rainbow brackets, including `[@ ... ]`, auto-closed brackets
  and quotes, and comment toggling (`cmd-/`) with `(* ... *)`;
- auto-indentation: the cases of a rule under it, the body of a case or of a
  function on the next line, the lines of a node that do not fit on one;
- text objects in vim mode: `af`/`if` for a rule function, a helper or a
  rule, `ac`/`ic` for a type, a node, a sort or a subsort, `gc` for a comment;
- snippets: `rule`, `case`, `casew`, `fn`, `extendrule`, `extendfn`, `prim`,
  `oracle`, `node`, `sort`, `subsort`, `notation`, `type`, `typer`, `infix`, `prefix`,
  `constant`, `use`, `usebuiltin`, `match`, `let`, `if`, `section`.

## Installing

Until it is published, install it as a dev extension: in Zed, run
`zed: install dev extension` from the command palette and pick this directory
(`editors/zed`). Zed compiles the extension (`src/lib.rs`) to WebAssembly, so
Rust must be installed with [rustup](https://rustup.rs) (Zed adds the
`wasm32-wasip2` target itself); it also fetches the grammar from GitHub, at the
commit `rev` of `extension.toml`, and compiles it. The extension needs Zed
0.205 or later (`zed_extension_api` 0.7).

To try a grammar that is not pushed yet, point `extension.toml` at the
checkout, temporarily:

```toml
[grammars.kanon]
repository = "file:///path/to/kanon"
rev = "<a local commit with the grammar>"
path = "tree-sitter-kanon"
```

and rebuild it with the `Rebuild` button of the extension, in `zed: extensions`.
`zed: open log` shows the errors of the queries.

## Language server

The extension starts `kanon lsp`, which speaks LSP over stdio. The binary is
not bundled: it is `lsp.kanon.binary.path` of Zed's settings if set, else the
`kanon` on the PATH of the project's shell, so that the one of an opam switch
or of a direnv is found. Install it with
`opam pin add kanon https://github.com/N1ark/kanon.git`, or `dune install`
from a checkout. To use another binary, in `settings.json` (or the project's
`.zed/settings.json`):

```json
{ "lsp": { "kanon": { "binary": { "path": "/path/to/kanon", "arguments": ["lsp"] } } } }
```

`arguments` defaults to `["lsp"]`, and `binary.env` adds variables to the
environment of the shell. `initialization_options` and `settings` are passed
on to the server. `zed: open log` shows why it did not start.

## Tasks

Zed's tasks can run `kanon` on the current file. In `.zed/tasks.json` (or the
global `tasks.json`, from `zed: open tasks`):

```json
[
  {
    "label": "kanon: generate the OCaml of $ZED_FILENAME",
    "command": "kanon ocaml \"$ZED_FILE\" > \"$ZED_DIRNAME/rules.gen.ml\"",
    "tags": ["kanon"]
  },
  {
    "label": "kanon: generate the OCaml types of $ZED_FILENAME",
    "command": "kanon ocaml-types \"$ZED_FILE\" > \"$ZED_DIRNAME/types.gen.ml\"",
    "tags": ["kanon"]
  }
]
```

## Layout

- `extension.toml`: the extension, its language server, and the grammar it
  uses;
- `Cargo.toml`, `src/lib.rs`: the Rust part of the extension, compiled to
  WebAssembly by Zed, which finds the `kanon` binary to start the language
  server (`Cargo.lock` is committed, `target/` is not);
- `languages/kanon/config.toml`: the language (file suffixes, comments,
  brackets, indentation);
- `languages/kanon/*.scm`: the tree-sitter queries: `highlights` (also used
  by `tree-sitter highlight` and the highlight tests of the grammar),
  `brackets`, `indents`, `outline`, `overrides` (the scopes of strings and
  comments, in which `"` does not auto-close) and `textobjects`;
- `snippets/kanon.json`: the snippets.
