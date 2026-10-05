# Changelog

## Unreleased

### Added

- [Scoped names](https://n1ark.github.io/kanon/reference.html#names): `Bitvec.add` from another module.
- The language server hovers, renames and completes qualified names.
- The tree-sitter grammar reads qualified names.
- [Typed functions](https://n1ark.github.io/kanon/reference.html#declarations): sort-annotated `fn` results.

### Changed

- Generated code qualifies names by module: `Rules.Bitvec.add`.
- Bool functions lose prefixes: `b_not` is `Bool.not_`.
- `ocaml-typed` generates only the module type `S`.
- `ocaml-tests` lists rule functions by qualified name.
- Destructors `as_foo` and `is_foo` live in their module.
- Primitives of different modules may not share a name.
- `Kanon_flat` is a reserved module name.
- `Foo.x` is a qualified name, not a field access.

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

### Removed

- `ocaml-check`: use [`ocaml-types`](https://n1ark.github.io/kanon/reference.html#ocaml).
- `type t`, `type ty` and `[@operators]`: declare nodes and sorts.
- Placing nodes in types by name.
- `[@ite]` and `[@distrib_ite]`: write their rules by hand.
- `[@to_term]` on boolean literals: use [`[@fold f lift]`](https://n1ark.github.io/kanon/reference.html#laws).
- The primitive `equal`: use `=`.
- The built-in `land`, `lor`, `lxor`, `lsl`, `lsr`, `asr` and `~`.
