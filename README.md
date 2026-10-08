<img src="site/public/favicon.svg" alt="" width="96" height="96" align="right" />

# Kanon

Kanon is a rule language for the simplifying smart constructors of a *value
language*: the functions that build its terms (`Bool.and_ a b`, `Bitvec.add c a b`,
...) and simplify them on the fly. The value language (its types, nodes,
literals, operators and their laws) is declared in `.knl` files and its rules
are written in `.kn` files, in a small, pure, first-order language whose syntax
is that of OCaml. Soteria's `Bv_values` and `Tiny_values` are written in Kanon.

From the rules, the `kanon` tool generates:

- OCaml: the types of the language with its hash-consed terms, the
  implementation of the rules, a typed interface of the smart constructors, and
  differential tests of the rule functions;
- Lean: a model of the rules, with one soundness statement per rule, and the
  proof that the whole simplifier is sound from the proofs of these statements.

## Example

```ocaml
(* tiny.knl *)
sort TInt
node Int of int : TInt
notation Int
node Plus : TInt -> TInt -> TInt [@comm] [@unit 0] [@fold add]
infix "+" = Plus, plus

(* tiny.kn *)
fn add (x y : int) : int = x + y

rule plus : Plus (v1, v2) =
  | assoc: (x + #a) + #b -> x + Int (a + b)
```

`[@fold]` and `[@unit]` give `plus` the rules that add two literals and drop a
zero, and `assoc` is written by hand. With `lang.knl` containing `use "tiny"`,
`kanon ocaml lang.knl` writes the OCaml of `plus` and `kanon lean-all DIR lang.knl`
the Lean model with its statements, under `DIR`.

## Build and use

Kanon needs OCaml >= 5.5 and dune (the dependencies are in `kanon.opam`):

```
opam install . --deps-only --with-test
dune build
dune test
dune exec -- kanon BACKEND FILE...
```

`kanon BACKEND FILE...` reads the language that the files declare and writes
the generated code on standard output. The backends are `ocaml-types`, `ocaml`,
`ocaml-typed`, `ocaml-tests`, the Lean files of the modules (`lean-types`,
`lean-node`, `lean-lang`, `lean-model`, `lean-statements`, `lean-soundness`) and
of the language (`lean-syntax`, `lean-semantics`, `lean-rules`);
`kanon lean-all DIR FILE...` writes the Lean files under `DIR`. `kanon lsp` runs the language server and
`kanon --version` prints the version. The Lean proofs build with `lake`, from
`lean/` (Kanon's Lean library) and from the `lean/` directory of an example.

## Documentation

The manual is the [site](https://n1ark.github.io/kanon/):

- the [Tutorial](https://n1ark.github.io/kanon/): a language built step by
  step, with the OCaml and the Lean that Kanon generates from each step;
- the [Reference](https://n1ark.github.io/kanon/reference.html): the
  declarations, attributes, operators, rules, backends and their outputs, and
  the language server;
- the [Guide to proofs](https://n1ark.github.io/kanon/proving.html): how to
  prove the Lean statements of a language, on `examples/ints/`;
- the [Sandbox](https://n1ark.github.io/kanon/sandbox.html): Kanon in the
  browser, with its language server and the output of every backend.

The sources of the site are in `site/src` (`reference/`, `proving/`,
`tutorial/`): that is where the documentation is written.

## Repository layout

- `src/`: the `kanon` tool (parser, checker, backends, language server);
- `ppx/`: the ppx `kanon.ppx_include_file`, which includes generated OCaml;
- `lean/`: Kanon's Lean library (`KanonCore`);
- `modules/`: the built-in modules (the bool module, `use builtin "bool"`);
- `examples/`: `bool`, `ints` and `division` (with Lean proofs), `arrays` and `traversals`;
- `test/`: cram and compilation tests;
- `site/` and `web/`: the website, and Kanon compiled to JavaScript for it;
- `tree-sitter-kanon/` and `editors/zed/`: the grammar and the Zed extension.

## Status

Kanon is experimental: its syntax and its output change between versions,
without compatibility. The version is in `dune-project`, and `CHANGELOG.md`
lists the user-facing changes of each version.
