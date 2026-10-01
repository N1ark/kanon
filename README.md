# Kanon

Kanon is a rule language for the simplifying smart constructors of a *value
language*: the functions that build its terms (`b_and a b`, `bv_add c a b`,
...) and simplify them on the fly. From the rules, the `kanon` tool generates:

- their OCaml implementation, meant to be included in the module that defines
  the terms;
- an OCaml check that the OCaml types of the language agree with its
  declaration;
- OCaml differential tests of the rule functions;
- a Lean model of the rules, with one soundness statement per rule, and the
  proof that the whole simplifier is sound from the proofs of these
  statements.

The value language (its types, nodes, literals, operators and their laws) is
declared, in `.knl` files: Kanon does not hard-code any. The targets are fixed:
OCaml, where terms are hash-consed (`Hc`) records `{ kind; ty }`, and Lean,
where they are `Term.mk kind ty`. Soteria's `Bv_values` and `Tiny_values` are
written in Kanon.

Kanon is a small, pure, first-order language with its own typing. Its syntax is
that of OCaml, apart from the declarations and rule names below.

## Usage

```
kanon BACKEND FILE...
```

reads the language declared by the files, usually its one `.knl` file, with
the modules it uses, and writes on standard output:

- `ocaml`: the OCaml implementation of the rule functions and helpers, in terms
  of a module `P` of primitives, which must be in scope where it is included;
- `ocaml-check`: the OCaml check of the types of the language (which only needs
  the `.knl` files);
- `ocaml-tests`: the differential tests (see [Tests](#tests));
- `lean-types`, `lean-syntax`, `lean-signatures`, `lean-typing`, `lean-model`,
  `lean-statements`, `lean-lifts`, `lean-soundness`: the generated Lean files
  (see [Proofs](#proofs)); `lean-all` writes each of them, `F.lean`, to
  `F.lean.gen` in the current directory.

A file uses a module with `use "path"`: the module's declarations are in
`path.knl` and its rules in `path.kn` (either may be missing), relative to the
directory of the file. `use +name` uses the module `name` built into `kanon`
(see [Modules and examples](#modules-and-examples)): `use +bool` reads
`modules/bool.knl` and `modules/bool.kn` from the binary, as `bool.knl` and
`bool.kn` (in the locations of errors and the headers of the generated
files). A module is read once, where it is first used; the declarations of a
file come before those of the modules it uses, and its rules after theirs. A
language `lang.knl` that starts with

```
use +bool
use "int"
```

is made of the bool module and of the module `int` (`int.knl` and `int.kn`),
and `kanon ocaml lang.knl` generates its rules.

The ppx `kanon.ppx_include_file` includes the generated OCaml:
`[%%include_file "rules.gen.ml"]` is the structure of `rules.gen.ml`, a file
next to the current one, as `include struct ... end`, so that it is compiled
along with its primitives.

## The language

A language is declared in `.knl` files, by `use`, `type`, `node`, `infix`,
`prefix` and `constant` items and floating attributes.

### Types

```ocaml
type var [@ocaml "Symex.Var.t"] [@lean "Int"] [@noeq]

type kind [@ocaml "t_kind"] [@noeq] =
  | Var of var
  | Bool
  | Int
  | Unop of unop * t [@operators]
  | Binop of binop * t * t [@operators]

type binop [@ocaml "Binop.t"] =
  | And
  | Plus

type checked = { signed : bool; unsigned : bool }

type ty = TBool | TInt
```

A type is abstract, a variant or a record. `kind` and `ty`, the kinds and types
of terms, must be declared; `t` (terms), `int` (arbitrary precision, `Z.t` in
OCaml), `bool`, `unit`, tuples, `option` and `list` are built in.

- `[@ocaml "..."]` gives the OCaml type, if it is not the Kanon name. The
  constructors of a type (and the fields of a record) are in its module, and
  those of `kind` and `ty` are the fields of terms.
- `[@lean "..."]` gives the Lean type, if it is not the Kanon name, CamelCased
  (`ext_ty` is `ExtTy`). Kanon generates the Lean definitions of the types,
  except for the abstract ones, which are defined by hand (in `R.Abstract`, see
  [Proofs](#proofs)) unless `[@lean]` names an existing type.
- `[@noeq]`: `=` and `<>` are not allowed at this type. `[@equal "f"]`: in
  OCaml, `=` is the primitive `P.f` rather than `Stdlib.( = )`.
- A `nat` argument of a constructor is an OCaml `int` (a width, an index), and
  an `int` in Kanon.
- `[@operators]` on a kind constructor: the constructors of the type of its
  first argument are node constructors too, `Add (c, l, r)` standing for
  `Binop (Add c, l, r)`.

### Modules and nodes

A language is made of the modules it uses (see [Usage](#usage)), each with its
declarations (`bool.knl`) and its rules, primitives and helpers (`bool.kn`).
The language itself declares its types, as its OCaml AST has them, in which
Kanon places the nodes of its modules.

- `node C ...`, in a module, declares the constructor `C` as a type would
  (`node And : TBool -> TBool -> TBool [@comm] [@idem]`). The module declares
  what the node is (its arguments, typing, laws and operators), and Kanon
  places it in the types of the language, in the order of the modules: an
  operator on `k` operands in the type of the operators of the
  `[@operators]` constructor of `kind` with `k` terms (`And` in `binop`, for
  `Binop of binop * t * t`), a sort that the typings use in `ty`, and the other
  nodes in `kind`. The language declares those types, as its OCaml AST has
  them, with their other constructors (`Var of var`, `TSeq of ty`); a type
  that only has nodes is declared without constructors (`type binop
  [@ocaml "Binop.t"]`). The language may also place a node itself, by naming
  it alone in a type (`type nop = Distinct`), which it must for a node with
  operands that Kanon does not place by their number, such as `Distinct` in
  `Nop of nop * t list`.
- A node placed in `kind` itself, rather than in a type of operators, has its
  operands as arguments (`Ite of t * t * t`).
- `extend rule f = | r: p -> e ...`, in the rules of a module, adds rules to the
  rule function `f` of a module below it, as if they were written in `f`: last,
  but before its final catch-all case `_`, or with `extend rule f before r`,
  before its rule `r`. A function's rules are tried in order, so this keeps the
  order of the rules independent of the modules they are written in.
- `extend fn f = | p -> e ...` adds cases to the helper `f` in the same way.
  The cases go into the match that ends `f`, behind `let`s and the right
  operands of `||` and `&&`.

### Attributes of nodes

The arguments of attributes are names, integers, `true` and `false`, or strings
for anything else (`[@fold f_add]`, `[@zero 0]`, `[@ocaml "Svalue_ast.Unop.t"]`).

- `[@comm]` on a binary operator: its operands commute.
- `C of a * b (x, y) : s1 -> s2 when e` on an operator: its typing, from which
  Kanon generates `T.WT` in `Typing.lean`. Its operands, then its result, have
  the sorts `s1`, `s2`, which are terms of `ty` over the arguments `x`, `y` of
  `C` and over free variables, under the condition `e`. A free variable stands
  for any sort where a sort is expected, and otherwise for any value of its
  type; a width (`nat` argument of a type) is positive, unless the condition
  constrains it.
- `[@literal]` on a kind constructor of one `bool`: the boolean literals, which
  `true` and `false` match. `[@to_term f]` gives the function that makes the
  literal of a boolean, for `[@fold]` (e.g. `of_bool`).
- `[@literal int]` on a kind constructor of one `int`: the integer literals,
  which `0`, `1`, ... and `#x` match; `#x` binds their integer.
- `[@literal t]` on a kind constructor of one `int`: integer literals whose
  values have the (abstract) type `t`, e.g. bit-vectors, which `#x` binds in
  rules (and their integer in helpers). The constructor then gives:
  - `[@to_term f]`: the function that makes the literal of a value, called
    where a value is used as a term (e.g. `lit`);
  - `[@of_term p]`: the primitive that reads the value of a literal (e.g.
    `bv_of_lit`);
  - `[@raw f p]`, any number of times: the primitive `p` computes `f`,
    whose last argument is a value, directly on the literal, without reading its
    value (e.g. `[@raw width lit_width]`).
- `[@ite]`: the node of conditionals, for `[@distrib_ite]`.
- `[@get f]` on a sort with one argument: the helper `f` reads that argument
  from the sort of a term (`node TBitVector of nat [@get size]`). Kanon then
  reads the argument with `f v`, rather than by matching the sort of `v`,
  where it infers the sort of a node or binds the variables of the sort of an
  operand (see [Rules](#rules)).
- Laws, see [Laws](#laws).

### Operators on terms

```ocaml
infix "+" = Add, bv_add unchecked, lit_add
infix "urem" = Rem false, bv_rem false, lit_urem
prefix "not" = Not, b_not
```

`infix "op" = Node, f args[, g]` declares what the operator builds and matches:
in expressions, `a + b` calls the smart constructor `f` with the leading
arguments `args` (`bv_add unchecked a b`); in patterns, it matches the node
(`Add (_, a, b)`, whatever its parameters); on the values of literals (see
`[@literal t]`), it is the primitive `g`. The operators are `+`, `-`, `*`,
`land`, `lor`, `lxor`, `lsl`, `lsr`, `asr`, `++`, `&&`, `||` and `==`, the
prefix `-`, `~` and `not`, and any word (`urem`), which is then an infix
operator, at the precedence of `*`, in the rest of the files (the declarations
of a module come before its rules, and before the modules it uses after them),
and no longer a name. Otherwise, the arithmetic and bitwise operators are those
of integers, and `&&`, `||` and `not` those of booleans.

The node of an operator may fix its parameters, as in `Rem false`: its patterns
then match only these (`a urem b` is `Rem (false, a, b)`), and in a rule on the
node, a case `p urem q` is the case `p, q` when the parameter of the spec is
`false`.

### Constants

```ocaml
constant "0" (v) = bv_zero (size v)
constant "true" (v) = v_true
```

`constant "c" (v) = e` is the term of the literal `c` (`0`, `1`, `true` or
`false`) at the type of the term `v`, for the laws `[@unit c]` and
`[@zero c]`.

### Lean

- `[@@@lean_root "R"]`: the namespace of the Lean model, and the root of its
  modules (`Kanon` by default).
- `[@@@lean_param "x" "T"]`: a parameter `x : T` of the semantics, which the
  statements quantify over (e.g. a semantics of floats).

`use`, `type`, `of`, `node`, `infix`, `prefix`, `constant`, `extend` and
`before` are keywords.

## Functions

```ocaml
rule bv_not : BvNot v =
  | lit: BitVec bv -> lit (lognot bv)
  | ite: Ite (b, l, r) -> b_ite b (bv_not l) (bv_not r)

fn size (v : t) : int [@ty_only] = size_of_ty (type_of v)
```

- Parameters and results are annotated; `(v1 v2 : t)` stands for
  `(v1 : t) (v2 : t)`.
- `rule f : e = | r: p -> body | ...` declares a *rule function*, which
  returns a term that must refine the raw term `e` (its spec). Its cases match
  the operands of the spec (its parameters of type `t` and `t list`, as a tuple
  when there are several), and each is a rule, named by the label before its
  pattern (`lit:`). A rule function may instead have an expression as its body,
  `rule f : e = expr`, with no rules. When the spec is
  a node over variables, `C (x1, ..., xn)`, they are the parameters of the
  function, at the types of the arguments of `C` (`v : t` above); otherwise the
  function declares its parameters, `rule f params : e = body`.
- Unless its last case matches anything, a rule function ends with the rule
  `default`, which builds its spec (`| default: _ -> BvNot v` above).
  A rule function without a body, `rule f : e`, only has the rules derived
  from the laws of its spec (see [Laws](#laws)) and `default`.
- `fn f params : ty = body` declares a helper. All functions can call each
  other. `[@ty_only]` marks a helper of one term that only reads its type (see
  [Rules](#rules)).
- `prim f : a -> b` declares a primitive, implemented by hand in `P` and in
  Lean (the generated OCaml and `Signatures.lean` check that both define it, at
  this type); `oracle f : a -> b` declares one that the Lean model takes as a
  parameter, so that the proofs may not rely on its behaviour (e.g. a
  hash-consing order).
- `type_of v` is the sort of the term `v`. It and the primitive `equal`
  (physical equality of hash-consed terms) are compiled to direct accesses of
  the terms in OCaml. `P` must also define `node`, `zcompare`,
  `zequal` and `equal_ty`.
- A language with commutative operators gets the oracle `tag_le` (the
  hash-consing order, compiled to a comparison of the tags in OCaml) and the
  helper `mk_commut_binop` (see [Terms](#terms)).

## Rules

- `#l` (or `C l`, for `C` the node of integer literals) binds `l` to the value
  of the literal.
- The pattern variables of a rule may not shadow the parameters of its
  function.
- A case that an earlier case without a guard already matches can never be
  taken: Kanon leaves it out (it does not look into guards, so a case with a
  guard, or with a repeated variable or an integer literal, which are checks
  too, covers nothing). The generated OCaml enables the warning on unused match
  cases, which would report any it missed.
- When the spec of a rule is a commutative node over `v1, v2` (e.g.
  `And (v1, v2)`), the cases match them in either order,
  unless the pattern is symmetric (the same once swapped, up to renaming), so
  `| true_: true, x -> x` covers both `true && x` and `x && true`. The cases
  must then name the operands rather than use `v1` and `v2` (other than as the
  argument of `type_of` and `[@ty_only]` helpers).
- The cases of a rule whose spec is a binary operator may also be written with
  the operator: in `rule bv_sub : Sub (checked, v1, v2)`,
  `| sub_sub: l - (l - r) -> r` stands for `| sub_sub: l, (l - r) -> r`.
- The operands of a spec have the sorts that the typing of its node gives
  them, which the generated OCaml asserts on entry to the rule function (so
  that the assertion is compiled out with `-noassert`), and the proofs assume.
  An operand may be annotated with its sort, `(v : TBitVector n)`, to also
  assert it and bind its variables in the rules:
  `rule bv_extract : BvExtract (from_, to_, (v : TBitVector sz))` uses `sz`
  for the width of `v`. A rule that also simplifies ill-typed specs is marked
  `[@untyped]` after its spec (`rule sem_eq_untyped : Eq (v1, v2) [@untyped]`),
  and asserts nothing.

## Laws

Attributes on an operator in its declaration declare its algebraic laws, from
which Kanon derives the first rules of its *rule function* (the rule function
whose spec is the operator over the function's parameters, e.g. `bv_mul` for
`Mul (checked, v1, v2)`), in this order, before the rules written by hand. The
derived rules are ordinary rules: they are generated and proved like the
others, and a hand-written rule may not reuse their names.

| law | derived rule, in `bv_add (checked) (v1 v2)`, `bv_sub`, `bv_neg`, ... |
|---|---|
| `[@fold f]` | `lits: #l + #r -> f l r`, `lit: #bv -> f bv` |
| `[@unit c]` | `zero: x + 0 -> x` (commutative), `zero: _ lsl 0 -> v1` (otherwise) |
| `[@zero c]` | `zero: _ * 0 -> bv_zero (size v1)`, `false_: _ && false -> v_false` |
| `[@idem]` | `same: v && v -> v` |
| `[@invol]` | `neg: -x -> x`, named after the operator (unary operators) |
| `[@distrib_ite]` | `ite: Ite (b, l, r) -> b_ite b (bv_neg checked l) (bv_neg checked r)` (unary operators) |

- `[@fold f]`: `f` takes the last parameters of the node that it has room
  for (`lit_extract from_ to_ bv`, `add_overflows signed l r`), then the
  literals, of the types of its arguments: the values of integer literals of
  type `t` (`[@literal t]`) are bound to `l` and `r` (to `t` for one
  operand), the others to the first letter of their type (`Float f1`,
  `Float f2`, `Float f`). A `bool` result is lifted with the `[@to_term]` of
  the boolean literals, and a result of another type `T` with its literal
  constructor, at the sort of the spec (`Float (f_add f1 f2)`).
- `[@unit c]` and `[@zero c]` take the literal `0`, `1`, `true` or `false`,
  which names the rule (`zero`, `one`, `true_`, `false_`), and whose term the
  language declares with `constant`. On an operator that does not commute, `c`
  is on the right; on one that does, the rule matches it on either side.
- `[@distrib_ite]` rebuilds the branches with the rule function itself, and the
  conditional (the node marked `[@ite]`) with its rule function.

## Terms

- Nodes build raw terms, without simplification: `BvNot v`, `Add (c, l, r)`.
  Their sort is inferred from their typing: the sort of their result when it
  only depends on their parameters (`TBool`), else the sort of an operand that
  has the same sort (`type_of v` for `BvNot v`), else the result over the
  sorts of the operands (`TBitVector (n + m)` for `BvConcat (l, r)`, from the
  sorts `TBitVector n` and `TBitVector m` of `l` and `r`).
- In rule functions, the operands of commutative operators are put in the
  hash-consing order: `And (v1, v2)` is the node of
  `mk_commut_binop And v1 v2`, which puts the operand with the smallest tag on
  the left.
- Operators are node constructors (see `[@operators]`). The long forms remain
  available.
- Patterns match the kind of a term directly: `Int z`, `Add (c, l, r)`.

## Patterns

- `0`, `1`, ... match integer literals, `#_` any of them, and `#x` binds one;
  `true` and `false` match boolean literals.
- A repeated variable matches equal terms: `| p, not p -> v_false`.
- The operands of commutative operators match in either order: `x + #k` also
  matches `#k + x`. The swap is left out when both operands are wildcards or
  variables bound nowhere else, as it matches the same terms.
- `p [@comm]` also matches the components of the pair `p` swapped (the
  arguments of the rule function): `(1, ~v) [@comm]` matches both `1, ~v` and
  `~v, 1`.
- Or-patterns, `as`, `when` guards, `Some`/`None`, lists and partial records
  (`{ unsigned = true; _ }`) are supported. Each alternative of an or-pattern is
  tried in turn, together with the guard.

## Proofs

The Lean files are generated in the namespace `R` of `[@@@lean_root]`:

- `Types.lean` and `Syntax.lean` define the types of the language, around
  `R.Abstract` (written by hand), and which operators commute (`Binop.Comm`,
  from `[@comm]`), and `Typing.lean` the typing of the operators.
- `Signatures.lean` checks that `R.Prims` defines the primitives, at their
  types.
- `Model.lean` is a Lean model of the rule functions, over the primitives.
- `Statements.lean` states that every alternative of every rule is sound: its
  result *refines* its spec (the raw term it simplifies).
- `Lifts.lean` states that the specs are monotone in their term arguments.
- `Soundness.lean` proves each rule from its alternatives, and every function
  from its rules, up to `R.opsN_sound`: the whole simplifier is sound.

They build on Kanon's Lean library, `lean/` (the package `kanon`, library
`KanonCore`, namespace `Kanon`, which they open), and on modules written by
hand for the language: `R.Abstract` (the abstract types), `R.Prims` (the
primitives), `R.Semantics` (the semantics of terms, the parameters of
`[@@@lean_param]`, the refinement `Refines`, `Ops.Sound`'s `Oracle.Compat`),
`R.Lib.Lift`, `R.Lib.Rule` and `R.Proofs` (the proofs).

The library gives what does not depend on the language:

- `whenSome` and `firstSome`, with which the model is written, and
  `orElse_some`;
- `Refinement R`, the class of refinement relations (reflexive and
  transitive), of which the language gives an instance for `Refines`, and the
  lemmas `Refinement.firstSome_nil` and `Refinement.firstSome_cons`, with which
  the soundness of a rule function follows from that of its rules;
- the attributes `kanon_spec` (the specs, which the rule tactics unfold),
  `kanon_tactic "tac"` (on the spec of a rule function: the tactic that proves
  its arms) and `kanon_arm` (on a theorem: the hand-written proof of an arm);
- `kanon_proof% X`, the proof of the arm `X`: its hand-written proof, or the
  tactic of its function, or `kanon_auto`; and the tactic `kanon_arm`, the proof
  of a rule from those of its arms.

The language gives the tactics `kanon_auto` (the default proof of an arm),
`kanon_comm` (refinement up to the order of the operands of commutative
operators) and `kanon_congr` (refinement by congruence), which the library
declares, with `macro_rules`.

An alternative (an arm) is one case of a rule, after expanding its or-patterns
and the swaps of commutative operands; its statement is over the variables of
its pattern, with its guard as a hypothesis (`f.r_name.arm.Stmt`). An arm is
named after the choices that produced it, so that reordering patterns does not
rename it: the head constructor (or operator) of each or-pattern branch taken,
with an index when both branches have the same head (`lt_leq`, `lt1`), and
`swap` for a swap (numbered when there are several), prefixed by `cN` when the
rule has several cases; an arm with no choice is `main`. An alternative that
only swaps commutative operands is proved from the unswapped one, if its guard
and body do not depend on the swap.

`KanonCore.Lang`, in the library, is a trial of a generic core: terms, their
evaluation and their refinement, for any language.

## Tests

`kanon ocaml-tests` generates, for every rule function, its spec, a call to it
and the name of the rule that fires, from random arguments, to be compared by
evaluation (soteria's `soteria/tests/bv_rules/` does so for `Bv_values`).

## Modules and examples

- `modules/bool.knl` and `modules/bool.kn` are an optional module of booleans:
  boolean literals, `Not`, `And`, `Or`, equality (`Eq`), conditionals (`Ite`)
  and `Distinct`, with their rules (the rule functions `b_not`, `b_and`,
  `b_or`, `b_ite`, `sem_eq`, `sem_eq_untyped` and `b_distinct`). They are built
  into `kanon`, as the module `+bool`. A language that uses the module places its nodes in its types, and declares the type `TBool`; the
  modules above it can add rules to its rule functions with `extend rule`, and
  literals to its helper `sure_neq` with `extend fn`. It is the bool module of
  soteria's `Bv_values` and `Tiny_values`.
- `examples/bool/` is a complete example language, made of the bool module
  alone, to start from: `lang.knl` declares its types and places the nodes of
  the module in them, and `lean/` is the Lean proof of its rules (the package
  `bool_example`, library `BoolExample`), which uses Kanon's library from this
  repository. Its generated files are committed: `dune test` checks that they
  are up to date (`dune promote` updates them). Its hand-written files are the
  semantics of the language (`Semantics.lean`: values are booleans, poison is
  `none`), its primitives (`Prims.lean`), the tactics of its proofs
  (`Lib/Lift.lean`: `kanon_congr`; `Lib/Rule.lean`: `kanon_comm` and
  `kanon_auto`, which proves an arm by case analysis on the values of the
  subterms it does not inspect) and the proofs of the arms of `b_distinct`
  (`Proofs.lean`). To check it:

  ```
  cd examples/bool/lean
  lake build
  lake env lean check_axioms.lean  # must not mention sorryAx
  ```
