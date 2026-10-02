# Changelog

## 0.2.0 (2026-10-02)

### Added

- [`notation C`](README.md#patterns) gives literal patterns to a leaf.
- [Helper parameters](README.md#functions) may be annotated with a sort.
- [`(C x : S args)`](README.md#terms) builds a node at an explicit sort.
- [Folds](README.md#laws) receive the sorts of the literals as `ty` parameters.
- An operator's function applies to any [non-term operands](README.md#operators-on-terms).
- [`[@ocaml]`](README.md#types) on records and variants re-exports an existing type.
- The site has a [guide to proofs](https://n1ark.github.io/kanon/proving.html) in Lean.

### Changed

- [Infix words](https://n1ark.github.io/kanon/reference.html#precedence) have the precedence of `*`.
- Built-in modules are used with [`use builtin "bool"`](README.md#usage).

### Removed

- `[@literal]`: use [`notation`](README.md#patterns).
- `[@to_term]`, `[@of_term]` and `[@raw]`: literals store integers or booleans.

## 0.1.0 (2026-10-02)

The first versioned release.

### Added

- `kanon --version` prints the version.
- [`ocaml-types`](README.md#ocaml): self-contained OCaml types and hash-consed terms.
- [`[@@@ocaml_prims "M"]`](README.md#floating-attributes) names the OCaml module of primitives.
- [`[@@@ocaml_types "M"]`](README.md#floating-attributes): the rules open the module of types.
- [`sort`](README.md#modules-nodes-and-sorts) declares sorts; `node` no longer does.
- [`node C : a list -> s`](README.md#modules-nodes-and-sorts) declares an operator of any arity.
- Any word or symbol sequence can be an [operator](https://n1ark.github.io/kanon/reference.html#operators).
- [`=` and `<>`](README.md#types) work at every type but `[@noeq]` ones.
- [`[@hash "M.hash"]`](README.md#types) hashes the values of an abstract type.
- [`[@fold f lift]`](README.md#laws): `lift` makes a term of the result.
- [Laws](README.md#laws) apply to `[@literal int]` literals.
- [`[@unit c]` and `[@zero c]`](README.md#laws) accept named constants.
- [`constant`](README.md#constants) and its parameter are optional.
- Lean: one proof per [commutative operator](README.md#proofs) proves swapped arms.
- The site has a [reference](https://n1ark.github.io/kanon/reference.html) of declarations, attributes and operators.

### Changed

- Kanon [generates the terms](README.md#modules-nodes-and-sorts) from the nodes and sorts.
- `[@literal]` is now `[@literal bool]`.
- `constant` takes a name or a literal: `constant 0 = e`.
- The rules of `[@unit c]` and `[@zero c]` are `unit_c`, `zero_c`.
- The generated rules call primitives in `[@@@ocaml_prims]`, not `P`.
- [Infix words](https://n1ark.github.io/kanon/reference.html#precedence) have the precedence of comparisons.

### Removed

- `ocaml-check`: use [`ocaml-types`](README.md#ocaml).
- `type t`, `type ty` and `[@operators]`: declare nodes and sorts.
- Placing nodes in types by name.
- `[@ite]` and `[@distrib_ite]`: write their rules by hand.
- `[@to_term]` on boolean literals: use [`[@fold f lift]`](README.md#laws).
- The primitive `equal`: use `=`.
- The built-in `land`, `lor`, `lxor`, `lsl`, `lsr`, `asr` and `~`.
