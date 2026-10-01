# Kanon for Zed

A [Zed](https://zed.dev) extension for Kanon, the `.kn` and `.knl` files, with
the grammar of `tree-sitter-kanon/`:

- syntax highlighting: keywords, the names of rule functions, helpers and
  primitives where they are defined and called, rule names (`| lit: ...`),
  constructors, types, attributes (`[@comm]`, `[@@@lean_root "R"]`), the
  operators on terms (`&&`, `land`, and the infix words of patterns such as
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
  rule, `ac`/`ic` for a type or a node, `gc` for a comment;
- snippets: `rule`, `case`, `casew`, `fn`, `extendrule`, `extendfn`, `prim`,
  `oracle`, `node`, `type`, `typer`, `infix`, `prefix`, `constant`, `use`,
  `match`, `let`, `if`, `section`.

## Installing

Until it is published, install it as a dev extension: in Zed, run
`zed: install dev extension` from the command palette and pick this directory
(`editors/zed`). Zed then fetches the grammar from GitHub, at the commit
`rev` of `extension.toml`, and compiles it to WebAssembly.

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
    "label": "kanon: check $ZED_FILENAME",
    "command": "kanon ocaml-check \"$ZED_FILE\"",
    "tags": ["kanon"]
  }
]
```

## Layout

- `extension.toml`: the extension, and the grammar it uses;
- `languages/kanon/config.toml`: the language (file suffixes, comments,
  brackets, indentation);
- `languages/kanon/*.scm`: the tree-sitter queries: `highlights` (also used
  by `tree-sitter highlight` and the highlight tests of the grammar),
  `brackets`, `indents`, `outline`, `overrides` (the scopes of strings and
  comments, in which `"` does not auto-close) and `textobjects`;
- `snippets/kanon.json`: the snippets.
