# Changelog

## Unreleased

### Added

- [`[@no_lean]`](README.md#functions) on a `fn` or a `prim` leaves it out of the Lean files. A function or rule that Lean models may not call it.
- [Operators with a word suffix](README.md#operators-on-terms): a symbol directly followed by a word is one operator, such as `<u` or `<=s` (`infix "<u" = Ult, bv_ult`, `a <u b`, `a <=s b`), at the precedence of its symbol. The tree-sitter grammar reads them too.
- [`[@total]`](README.md#functions) on a `fn` requires a case for every node of the language, so that a node added without one is an error, not a silent fall through. It is checked after the `extend fn` cases are added.
- [Documentation comments](README.md#documentation-comments) `(** ... *)` on declarations, carried to the generated OCaml and Lean.
- `nat` is accepted in the signatures of functions, rules and primitives and in record fields, as a synonym of `int`. Primes in identifiers (`l'`) are covered by a test.

### Fixed

- The hover of the language server on a function or a node showed the second star of its documentation comment `(** ... *)` as text.
- `kanon ocaml-tests` listed the single rule `main` for a rule function whose spec annotates the sort of an operand (`(v : TBv sz)`), and its `fired` did not bind the variables of the sorts: it lists the rules and binds them.
- The literals that `[@fold]` binds are renamed when their names (`i`, `i1`, `i2`, derived from the type of the fold function) are those of a parameter of the node, which they captured: `node BvExtract of nat * nat (i, j) ... [@fold f]` passed the wrong values to `f`.

### Changed

- `[@ty_only]` on a rule is an error: it only means something on a helper (`fn`).
- Operators need spaces: an operator is surrounded by spaces (or brackets), and `x<y`, `x +y` or `f x+1` are errors, no longer `x < y`. A prefix operator (`-`, or a symbol that starts with `!`, `~` or `?`) is written right before its operand (`-x`, `x - -y`), and has no word suffix; `.`, `:` and `#` need no spaces. A symbol followed by a word is one operator whatever the declarations: the lexer no longer knows them (but for the words declared infix, such as `urem`).
- `use +name` is a syntax error like any other, not a message: it is `use builtin "name"`.
- A tuple of blanks (`_, _`) is a final catch-all case like `_`, for `extend fn`, `extend rule`, `default` and unreachable cases: the cases of `extend fn` were silently dropped after a final `| _, _ ->`.
- An `extend` case that is not added, because an earlier case matches everything it does, is an error.
- Unknown attributes on `fn`, `prim` and `rule` are errors.

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
