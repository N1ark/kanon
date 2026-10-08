# Changelog

## Unreleased

### Added

- [Scoped names](https://n1ark.github.io/kanon/reference.html#names): `Bitvec.add` from another module.
- The language server hovers, renames and completes qualified names.
- The tree-sitter grammar reads qualified names.
- [Traversals](https://n1ark.github.io/kanon/reference.html#traversals): `[@@@traversals]` generates `map_children`, `iter_children` and more.
- Node typings may give a computed result sort.
- [Typed functions](https://n1ark.github.io/kanon/reference.html#declarations): sort-annotated `fn` results.
- `kanon_on_refines tac` runs `tac` on refinement goals only.
- [`[@lean_heartbeats n]`](https://n1ark.github.io/kanon/reference.html#on-functions) bounds each generated arm proof.
- [`[@lean_proofs "F"]`](https://n1ark.github.io/kanon/reference.html#on-functions) imports `Proofs/F.lean` instead of `Proofs.lean`.
- `[@lean_proofs "F"]` also on `extend` items and `[@comm]` nodes.
- `kanon lean-all --check DIR` checks the Lean files are current.
- `[@extensible]` marks helpers that other modules extend.
- Example `two_langs`: four languages share modules, with a diamond.
- Modules that use each other are an error.
- [`[@lean_inv "P"]`](https://n1ark.github.io/kanon/reference.html#on-sorts): invariants of sorts and nodes, in their typing.
- `kanon_refl`: reflexivity of refinement, without evaluating terms.
- `kanon_refl` unfolds helpers, so a helper spec is refined.
- [Data types](https://n1ark.github.io/kanon/proving.html#data) of modules, in `R/Types.lean`.
- [Every module](https://n1ark.github.io/kanon/proving.html#modules) is proved once in Lean, for every language.
- `[@@@lean_root "R"]` in a module sets its Lean root.
- Hand-written `Sem`, `Prims` and `Proofs` files per module.
- Helpers may recurse on terms, decreasing by `Sem.size`.
- Lean backends `lean-node`, `lean-lang`, `lean-semantics`, `lean-rules`.
- Lean sorts and nodes may take sorts: `Srt Ty`.
- Lean binders: nodes may evaluate children in other environments.
- Cases of extensible helpers may call rule functions and helpers.
- Example `two_langs`: a pack module, with a quantifier.
- Lean children inside arrays, options, tuples and data types.
- Lean data types may hold terms: `Two T`.
- `[@@@lean_laws]`: a module's proofs assume facts each language proves.
- Lean `Node.children` lists the children of a node.
- Lifting lemmas hold of specs that read their arguments' sorts.

### Changed

- Generated code qualifies names by module: `Rules.Bitvec.add`.
- Bool functions lose prefixes: `b_not` is `Bool.not_`.
- `ocaml-typed` generates only the module type `S`.
- `ocaml-tests` lists rule functions by qualified name.
- Destructors `as_foo` and `is_foo` live in their module.
- Primitives of different modules may not share a name.
- `Kanon_flat` is a reserved module name.
- `Foo.x` is a qualified name, not a field access.
- [`kanon lean-all DIR`](https://n1ark.github.io/kanon/reference.html#lean) writes a few Lean files per module.
- Languages write `Val.lean` and `Typing.lean` by hand.
- `Node.eval` gets the children's values in every environment.
- Lean invariants take the arguments of the typing.
- Removed backends `lean-signatures`, `lean-typing`, `lean-lifts`, `lean-nodes`.
- Removed `[@@@lean_param]`.
- A module's `Oracle.Compat` is over any semantics `S`.
- Lean backends print every file of their part.
- More arms that swap commutative operands are derived.
- The bool module's Lean proofs move to library `KanonBool`.
- `kanon_tactic` on `Ops` proves a module's extension arms.
- `[@lean "N"]` names generated records and variants.
- [Lean statements and proofs](https://n1ark.github.io/kanon/proving.html#files): a file per function.

### Fixed

- Rule soundness unfolds functions whose equation lemmas fail.
- Commuted arms reading a swapped term's type are proved directly.
- `kanon_proof%` finds the `kanon_tactic` of qualified functions.
- `@[kanon_arm]` proofs of a file elaborate in parallel.
- `kanon_lift` leaves subsort predicates as goals instead of failing.
- `kanon_congr` needs `kanon_congr_side` to close its goal.
- `kanon_lift_body` lifts calls under goals that `split` tagged.
- `kanon_comm` and `kanon_congr` fail fast on different terms.
- Record literals in Lean use the Lean name of their type.
- `kanon_lift` finds a module's lemmas inside its arm proofs.
- `-(-5)` is `5`, not a crash.
- `ocaml-typed` accepts sort variables like `a'`.
- Generated term equality works beside a module named `Int`.
- Record fields may be named `kind`, `ty` or `tag`.
- Types named like OCaml's (`string`) are an error.
- Variables named like a function's OCaml name are an error.
- Variables and local functions shadow each other, as in OCaml.
- Literals and repeated variables work in `let` patterns.
- OCaml keywords like `end` and `to` are valid names.
- `ocaml-tests` compiles when a rule parameter is named `src`.
- Doc comments with a lone quote after a letter compile.
- Doc comments with character literals and `{%ext|` compile.
- Generated types call `Stdlib.Int`, not a module named `Int`.
- A case of variables like `x, y` hides later cases.
- `ocaml-typed` keeps the order of a rule's parameters.
- `ocaml-tests` builds with unused-case warnings as errors.
- Languages with one sort build with warnings as errors.
- A file named `z` is an error: `Z` is Zarith's.
- A module named like the `ocaml_prims` module is an error.
- Rules named like Lean keywords generate valid Lean.
- Lifting lemmas of keyword-named parameters are valid Lean.
- Lean keywords like `exists` and `try` are quoted.
- Record fields named like Lean keywords are quoted.
- Modules named like Lean keywords generate valid Lean.
- `Node.Rel` is valid for node arguments `x` and `x'`.
- `lean-node` rejects node arguments named `f`, `y` or `ev`.
- Lean files import the modules whose types a module mentions.
- Lean rejects rule parameters named `h`, `hO`, `res` or `sem`.
- `kanon lean-all` rejects two modules with the same Lean root.
- `kanon_arm` proves rules of functions with annotated operands.
- Lean typings of nodes whose sorts take sorts are valid.
- Typings are valid Lean with a node named `Int`.
- `Node.All`, `Rel` and `children` are valid with nodes named `True`.
- Lean rejects a pattern variable named as another parameter.
- Lean rejects an `as` variable named as another parameter.
- Lean rejects a module `List` with list-of-terms nodes.
- Rule functions without parameters are valid Lean.
- Helpers without parameters that need the model are valid Lean.
- Lifting lemmas prime the parameters `x` and `x'` apart.

## 0.3.0 (2026-10-04)

### Added

- [`[@no_lean]`](https://n1ark.github.io/kanon/reference.html#on-functions) leaves a `fn` or `prim` out of Lean.
- [Operators with a word suffix](https://n1ark.github.io/kanon/reference.html#operators), such as `<u` and `<=s`.
- [`[@total]`](https://n1ark.github.io/kanon/reference.html#on-functions) requires a case for every node.
- [Documentation comments](https://n1ark.github.io/kanon/reference.html#declarations) `(** ... *)` reach generated OCaml and Lean.
- [Computed sorts](https://n1ark.github.io/kanon/reference.html#terms): `(C x : e)`.
- `nat` is accepted in signatures and record fields.
- [Arrays](https://n1ark.github.io/kanon/reference.html#arrays): `t array` and `[| a; b |]`.
- [Subsorts](https://n1ark.github.io/kanon/reference.html#subsort): `subsort TNonzero of nat : TBitVector n`.
- [Subsorts in Lean](https://n1ark.github.io/kanon/reference.html#on-sorts): `[@lean "P"]` names a predicate.
- The [`ocaml-typed` backend](https://n1ark.github.io/kanon/reference.html#typed) generates a typed interface with phantom tags.
- The `ocaml` backend generates destructors `as_foo` and tests `is_foo`.

### Fixed

- Hover showed a stray star in documentation comments.
- `ocaml-tests` listed one rule for operands annotated with a sort.
- `[@fold]` passed wrong values when its literals shadowed node parameters.
- `extend fn` dropped cases after a `_, _` catch-all.

### Changed

- `[@ty_only]` on a rule is an error.
- Operators need spaces: `x<y` is an error.
- Prefix operators are written `-x`, with no space.
- `use +name` is a syntax error: write `use builtin "name"`.
- Parenthesised types in `(e : t)` are a syntax error.
- An `extend` case that is never added is an error.
- Unknown attributes on `fn`, `prim` and `rule` are errors.

## 0.2.0 (2026-10-02)

### Added

- [`notation C`](https://n1ark.github.io/kanon/reference.html#patterns) gives literal patterns to a leaf.
- [Helper parameters](https://n1ark.github.io/kanon/reference.html#on-functions) may be annotated with a sort.
- [`(C x : S args)`](https://n1ark.github.io/kanon/reference.html#terms) builds a node at an explicit sort.
- [Folds](https://n1ark.github.io/kanon/reference.html#laws) receive the sorts of the literals as `ty` parameters.
- An operator's function applies to any [non-term operands](https://n1ark.github.io/kanon/reference.html#operators).
- [`[@ocaml]`](https://n1ark.github.io/kanon/reference.html#on-types) on records and variants re-exports an existing type.
- The site has a [guide to proofs](https://n1ark.github.io/kanon/proving.html) in Lean.

### Changed

- [Infix words](https://n1ark.github.io/kanon/reference.html#precedence) have the precedence of `*`.
- Built-in modules are used with [`use builtin "bool"`](https://n1ark.github.io/kanon/reference.html#use).

### Removed

- `[@literal]`: use [`notation`](https://n1ark.github.io/kanon/reference.html#patterns).
- `[@to_term]`, `[@of_term]` and `[@raw]`: literals store integers or booleans.

## 0.1.0 (2026-10-02)

The first versioned release.

### Added

- `kanon --version` prints the version.
- [`ocaml-types`](https://n1ark.github.io/kanon/reference.html#ocaml): self-contained OCaml types and hash-consed terms.
- [`[@@@ocaml_prims "M"]`](https://n1ark.github.io/kanon/reference.html#floating) names the OCaml module of primitives.
- [`[@@@ocaml_types "M"]`](https://n1ark.github.io/kanon/reference.html#floating): the rules open the module of types.
- [`sort`](https://n1ark.github.io/kanon/reference.html#declarations) declares sorts; `node` no longer does.
- [`node C : a list -> s`](https://n1ark.github.io/kanon/reference.html#declarations) declares an operator of any arity.
- Any word or symbol sequence can be an [operator](https://n1ark.github.io/kanon/reference.html#operators).
- [`=` and `<>`](https://n1ark.github.io/kanon/reference.html#on-types) work at every type but `[@noeq]` ones.
- [`[@hash "M.hash"]`](https://n1ark.github.io/kanon/reference.html#on-types) hashes the values of an abstract type.
- [`[@fold f lift]`](https://n1ark.github.io/kanon/reference.html#laws): `lift` makes a term of the result.
- [Laws](https://n1ark.github.io/kanon/reference.html#laws) apply to `[@literal int]` literals.
- [`[@unit c]` and `[@zero c]`](https://n1ark.github.io/kanon/reference.html#laws) accept named constants.
- [`constant`](https://n1ark.github.io/kanon/reference.html#constant) and its parameter are optional.
- Lean: one proof per [commutative operator](https://n1ark.github.io/kanon/proving.html#loop) proves swapped arms.
- The site has a [reference](https://n1ark.github.io/kanon/reference.html) of declarations, attributes and operators.

### Changed

- Kanon [generates the terms](https://n1ark.github.io/kanon/reference.html#declarations) from the nodes and sorts.
- `[@literal]` is now `[@literal bool]`.
- `constant` takes a name or a literal: `constant 0 = e`.
- The rules of `[@unit c]` and `[@zero c]` are `unit_c`, `zero_c`.
- The generated rules call primitives in `[@@@ocaml_prims]`, not `P`.
- [Infix words](https://n1ark.github.io/kanon/reference.html#precedence) have the precedence of comparisons.
- Guards of commutative patterns are tried on swapped operands.
- A file given twice, as `m.kn` and `./m.kn`, loads once.
- A missing or unreadable input file is an error, not an exception.

### Removed

- `ocaml-check`: use [`ocaml-types`](https://n1ark.github.io/kanon/reference.html#ocaml).
- `type t`, `type ty` and `[@operators]`: declare nodes and sorts.
- Placing nodes in types by name.
- `[@ite]` and `[@distrib_ite]`: write their rules by hand.
- `[@to_term]` on boolean literals: use [`[@fold f lift]`](https://n1ark.github.io/kanon/reference.html#laws).
- The primitive `equal`: use `=`.
- The built-in `land`, `lor`, `lxor`, `lsl`, `lsr`, `asr` and `~`.
