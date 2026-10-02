# Kanon

Kanon is a rule language for the simplifying smart constructors of a *value
language*: the functions that build its terms (`b_and a b`, `bv_add c a b`,
...) and simplify them on the fly. From the rules, the `kanon` tool generates:

- the OCaml types of the language, with its hash-consed terms;
- the OCaml implementation of the rules;
- OCaml differential tests of the rule functions;
- a Lean model of the rules, with one soundness statement per rule, and the
  proof that the whole simplifier is sound from the proofs of these
  statements.

The value language (its types, nodes, literals, operators and their laws) is
declared, in `.knl` files: Kanon does not hard-code any. The targets are fixed:
OCaml, where terms are hash-consed records `{ kind; ty; tag }`, and Lean,
where they are `Term.mk kind ty`. Soteria's `Bv_values` and `Tiny_values` are
written in Kanon.

Kanon is a small, pure, first-order language with its own typing. Its syntax is
that of OCaml, apart from the declarations and rule names below. The
[site](https://n1ark.github.io/kanon/) has a tutorial, a reference of the
declarations, attributes and operators, and a sandbox.

## Usage

```
kanon BACKEND FILE...
```

reads the language declared by the files, usually its one `.knl` file, with
the modules it uses, and writes on standard output:

- `ocaml-types`: the types of the language and its terms, a standalone OCaml
  file that only needs Zarith (and only the `.knl` files, see [OCaml](#ocaml));
- `ocaml`: the OCaml implementation of the rule functions and helpers, which
  needs the types in scope;
- `ocaml-typed`: the OCaml interface of the smart constructors, where terms
  are typed by ghost tags (see [Typed OCaml](#typed-ocaml));
- `ocaml-tests`: the differential tests (see [Tests](#tests));
- `lean-types`, `lean-syntax`, `lean-signatures`, `lean-typing`, `lean-model`,
  `lean-statements`, `lean-lifts`, `lean-soundness`: the generated Lean files
  (see [Proofs](#proofs)); `lean-all` writes each of them, `F.lean`, to
  `F.lean.gen` in the current directory.

`kanon --version` prints the version of Kanon (see the
[changelog](CHANGELOG.md)).

A file uses a module with `use "path"`: the module's declarations are in
`path.knl` and its rules in `path.kn` (either may be missing), relative to the
directory of the file. `use builtin "name"` uses the module `name` built into
`kanon` (see [Modules and examples](#modules-and-examples)): `use builtin
"bool"` reads
`modules/bool.knl` and `modules/bool.kn` from the binary, as `bool.knl` and
`bool.kn` (in the locations of errors and the headers of the generated
files). A module is read once, where it is first used; the declarations of a
file come before those of the modules it uses, and its rules after theirs. A
language `lang.knl` that starts with

```
use builtin "bool"
use "int"
```

is made of the bool module and of the module `int` (`int.knl` and `int.kn`),
and `kanon ocaml lang.knl` generates its rules.

The ppx `kanon.ppx_include_file` includes the generated OCaml:
`[%%include_file "rules.gen.ml"]` is the structure of `rules.gen.ml`, a file
next to the current one, as `include struct ... end`, so that it is compiled
along with the types it needs (see [OCaml](#ocaml)).

## The language

A language is declared in `.knl` files, by `use`, `type`, `sort`, `node`,
`notation`, `infix`, `prefix` and `constant` items and floating attributes. The
[reference](https://n1ark.github.io/kanon/reference.html) lists them, with
every attribute.

### Documentation comments

A comment `(** ... *)` right before a `type`, `sort`, `node`, `prim`, `oracle`,
`fn` or `rule` documents it: the generated OCaml carries it as `(** ... *)` and
the generated Lean as `/-- ... -/`. A plain comment `(* ... *)` is ignored.

```ocaml
(** The sum of two integers. *)
node Add : TInt -> TInt -> TInt
```

### Types

```ocaml
type var [@ocaml "Symex.Var.t"] [@lean "Int"] [@equal "Symex.Var.equal"]
    [@hash "Symex.Var.hash"]

type checked = { signed : bool; unsigned : bool }
```

A type is abstract, a variant or a record: the types of the arguments of nodes
and of the helpers. `int` (arbitrary precision, `Z.t` in OCaml), `bool`,
`unit`, tuples, `option` and `list` are built in. `t`, the type of terms, and
`ty`, the type of their sorts, are generated from the nodes and the sorts (see
[below](#modules-nodes-and-sorts)), and cannot be declared.

- `[@ocaml "..."]` gives the OCaml type of an abstract type, which
  `ocaml-types` needs. On a record or a variant, it is optional: `ocaml-types`
  then re-exports that type (`type checked = M.checked = { ... }`), which
  OCaml checks against the declaration; otherwise it generates the type, with
  its Kanon name.
- `[@lean "..."]` gives the Lean type, if it is not the Kanon name, CamelCased
  (`ext_ty` is `ExtTy`). Kanon generates the Lean definitions of the types,
  except for the abstract ones, which are defined by hand (in `R.Abstract`, see
  [Proofs](#proofs)) unless `[@lean]` names an existing type.
- `=` and `<>` are allowed at every type, but at an abstract type marked
  `[@noeq]` (and the tuples, options and lists of it). Terms are compared as
  hash-consed terms (by their tags in OCaml), never with `Stdlib.( = )`.
- On an abstract type `a`, `[@equal "M.equal"]` gives the OCaml function
  `M.equal : a -> a -> bool` that decides `=` (`Stdlib.( = )` by default), and
  `[@hash "M.hash"]` the function `M.hash : a -> int` that hashes its values
  for hash-consing (`Hashtbl.hash` by default).
- A `nat` argument of a node or a sort is an OCaml `int` (a width, an index),
  and an `int` in Kanon.

### Modules, nodes and sorts

A language is made of the modules it uses (see [Usage](#usage)), each with its
declarations (`bool.knl`) and its rules, primitives and helpers (`bool.kn`).

- `node C ...` declares the constructor `C` of terms
  (`node And : TBool -> TBool -> TBool [@comm] [@idem]`): its arguments,
  typing, laws and operators. A node without operands (`node Var of var`,
  `node Bool of bool : TBool`) is a *leaf*; one with `k`
  operands in its typing is an *operator* of arity `k`; one whose only operand
  sort is a list (`node Distinct : a list -> TBool`, whose operands all have
  the sort `a`) an operator of any arity. `s list` is only allowed there.
- `sort S ...` declares a sort, a constructor of `ty`
  (`sort TBitVector of nat [@get size]`). Sorts and nodes are constructors:
  their names differ.
- `notation C` gives literal patterns to the leaf `C` of one `bool` or `int`
  (see [Patterns](#patterns)).
- `extend rule f = | r: p -> e ...`, in the rules of a module, adds rules to the
  rule function `f` of a module below it, as if they were written in `f`: last,
  but before its final catch-all case `_`, or with `extend rule f before r`,
  before its rule `r`. A function's rules are tried in order, so this keeps the
  order of the rules independent of the modules they are written in.
- `extend fn f = | p -> e ...` adds cases to the helper `f` in the same way.
  The cases go into the match that ends `f`, behind `let`s and the right
  operands of `||` and `&&`. The final catch-all case is `_`, or a tuple of
  blanks, which is strictly equivalent (`_, _`, `_, _, _`, `(_, _), _`): the
  cases are added before it, however it is written. `x, _` and `_ as x` are not
  blanks. A case that is not added, because an earlier case already matches
  everything it does, is an error. An `extend` of a `[@no_lean]` function adds
  cases that Lean does not model either.

Kanon generates the terms from the nodes, in the order of the modules. Their
kinds are the leaves, then, for each arity used, the operators of that arity,
in a type `opk` (with their other arguments: `Add of checked`) under a
constructor `Opk`: `Op1 of op1 * t`, `Op2 of op2 * t * t`, ..., and
`OpN of opn * t list`. In Lean, they are `Kind.Op2 Op2.And a b`. The rules do
not name them: they write `And (a, b)` or `a && b`.

### Attributes of nodes

The arguments of attributes are names (of functions, nodes and constants),
integers, `true` and `false`, or strings for anything else (`[@fold f_add]`,
`[@zero 0]`, `[@ocaml "Bv.t"]`).

- `[@comm]` on a binary operator: its operands commute (see [Terms](#terms)
  and [Proofs](#proofs)).
- `C of a * b (x, y) : s1 -> s2 when e` on an operator: its typing, from which
  Kanon generates `T.WT` in `Typing.lean`. Its operands, then its result, have
  the sorts `s1`, `s2`, which are terms of `ty` over the arguments `x`, `y` of
  `C` and over free variables, under the condition `e` (optional). A free
  variable stands for any sort where a sort is expected, and otherwise for any
  value of its type, and a repeated one for the same (`node Eq : a -> a ->
  TBool`); a width (`nat` argument of a type) is positive, unless the condition
  constrains it.
- `[@ghost tag]` on a sort, and `[@ghost "t1" ... "tn"]` on a node: the ghost
  tags of `ocaml-typed`, and `[@ctor f]`: the name of the smart constructor of a
  node (see [Typed OCaml](#typed-ocaml)).
- `[@get f]` on a sort with one argument: the helper `f : t -> int` reads that
  argument from the sort of a term (`sort TBitVector of nat [@get size]`). Kanon then
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
(`Add (_, a, b)`, whatever its parameters); on operands that are not terms and
have the types of the arguments of `g`, it is `g` (with
`infix "land" = BitAnd, bv_and, z_land`, `a land b` on integers is
`z_land a b`). An operator with a built-in meaning on a type cannot have a `g`
on that type. `prefix "op" = Node, f args[, g]` is
the same for one operand.

An operator is a word (`urem`) or, as in OCaml, a sequence of the symbols
`! $ % & * + - . / : < = > ? @ ^ | ~`, of `#` after the first, and of
non-ASCII characters (`≤`, `⊕`), read as long as possible. The reserved `=`,
`|`, `->`, `<-`, `:`, `::`, `;` and `.` cannot be declared, nor `<>`, built in
at every type. Its first character gives its precedence, as in OCaml; from the
lowest:

- `||` (right), `&&` (right);
- `=...`, `<...`, `>...`, `|...`, `&...`, `$...`, `!=` and the operators that
  start with a non-ASCII character (left);
- `@...`, `^...` (right); `::` (right);
- `+...`, `-...` (left); `*...`, `/...`, `%...` and the words (left);
  `**...` (right);
- the prefix `-`; the prefix `!...`, `~...` and `?...`.

The prefix operators are `-`, `not` and the symbols that start with `!`, `~`
or `?`. A word is an infix operator, and no longer a name, from its
declaration on: in the rest of the files (the declarations of a module come
before its rules, and before the modules it uses after them). Otherwise,
`+`, `-`, `*`, the prefix `-`, `<`, `<=`, `>` and `>=` are those of integers,
and `&&`, `||` and `not` those of booleans; the others must be declared.

The node of an operator may fix its parameters, as in `Rem false`: its patterns
then match only these (`a urem b` is `Rem (false, a, b)`), and in a rule on the
node, a case `p urem q` is the case `p, q` when the parameter of the spec is
`false`.

### Constants

```ocaml
constant 0 (v) = bv_zero (size v)
constant true = v_true
constant ones (v) = bv_ones (size v)
```

`constant c (v) = e` is the term of the constant `c` at the sort of the term
`v`, and `constant c = e` at any sort, for the laws `[@unit c]` and
`[@zero c]`. `c` is a literal, `0`, `1`, `true` or `false` (also written
`"0"`, ...), or a name. The constant of a literal is optional: Kanon otherwise
builds the node of its notation at the sort of the spec (`Bool false`,
`Int 0`).

### Floating attributes

- `[@@@ocaml_prims "M"]`: the OCaml module of the primitives (see
  [OCaml](#ocaml)), required when the language has primitives.
- `[@@@ocaml_types "M"]`: the OCaml module of the types, which the generated
  rules open (see [OCaml](#ocaml)).
- `[@@@ghost "name" "type"]`: a ghost tag type of `ocaml-typed`, `type name =
  type` in its signature, e.g. `[@@@ghost "sint" "[ `NonZero | `Zero ]"]`; the
  name may have type parameters (`"'a sseq"`). The tags are in order of
  declaration, and may mention each other. The bool module declares `sbool`.
- `[@@@lean_root "R"]`: the namespace of the Lean model, and the root of its
  modules (`Kanon` by default).
- `[@@@lean_param "x" "T"]`: a parameter `x : T` of the semantics, which the
  statements quantify over (e.g. a semantics of floats).

`use`, `type`, `sort`, `of`, `node`, `notation`, `infix`, `prefix`,
`constant`, `extend` and `before` are keywords.

## Functions

```ocaml
rule bv_not : BvNot v =
  | not: BvNot x -> x
  | ite: Ite (b, l, r) -> b_ite b (bv_not l) (bv_not r)

fn size (v : t) : int [@ty_only] = size_of_ty (type_of v)
```

- Parameters and results are annotated; `(v1 v2 : t)` stands for
  `(v1 : t) (v2 : t)`.
- `rule f : e = | r: p -> body | ...` declares a *rule function*, which
  returns a term that must refine the raw term `e` (its spec). Its cases match
  the operands of the spec (its parameters of type `t` and `t list`, as a tuple
  when there are several), and each is a rule, named by the label before its
  pattern (`not:`). A rule function may instead have an expression as its body,
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
  [Rules](#rules)). `[@no_lean]` (after the result type) leaves it out of the
  Lean model: it is checked and generated in OCaml as usual, but has no `def` in
  `Model.lean`, and no statement, lift or soundness entry, so it is for
  analysis and infrastructure code that is not a simplification rule (see
  [Proofs](#proofs)). A function or rule that Lean models may not call a
  `[@no_lean]` function or primitive (`rule bv_add calls f, which is
  [@no_lean]`), but a `[@no_lean]` function may call anything. Only `fn` and
  `prim` can be `[@no_lean]`: not rules, oracles, sorts, nodes or types.
  `[@total]` (on a `fn` only, and it combines with `[@no_lean]`) makes the
  function a per-node function that must have a case for every node of the
  language, leaf or operator, so that a node added without a case is an error
  and not a silent fall through (`fn operands (v : t) : t list [@total] = match
  v with | Int _ -> [] | a + b -> [a; b] | ...`). The check runs once, on the
  final language, after all the modules are loaded and the cases of every
  `extend fn` are added, so a module that adds nodes, even one used after the
  function, satisfies it with an `extend fn`, which appends its cases to the
  match (a `[@total]` function has no final catch-all case to go before). The
  function matches on its first parameter of type `t` (its body ends with a
  match on it, behind `let`s, possibly among other scrutinees). A node is
  covered by a case without a guard whose pattern on the term is the node, alone
  or in an or-pattern, with arguments and operands that match anything (`Int _`
  does, `Int 0` and `Sub (a, 0)` do not), and whose other patterns match
  anything. A case that matches any term (`_`, a variable, with or without a
  guard) is an error, since it would hide the missing nodes. The error lists all
  the missing nodes, leaves first and then operators, in the order of their
  declaration, at the function. Other
  attributes on `fn`, `prim` and `rule` are errors (a rule has `[@untyped]` and
  `[@ghost]`). A parameter of type `t` may be annotated with its sort
  instead, `fn msb_of (v : TBitVector n) : int`: the variables of the sort are
  bound in the body, the generated OCaml asserts the sort on entry, and the
  literals of patterns on `v` resolve with it (see [Patterns](#patterns)).
- `prim f : a -> b` declares a primitive, implemented by hand in OCaml, in the
  module of `[@@@ocaml_prims]` (see [OCaml](#ocaml)), and in Lean (the
  generated OCaml and `Signatures.lean` check that both define it, at this
  type), unless it is marked `[@no_lean]` after its type
  (`prim hash : t -> int [@no_lean]`), which Lean does not define or check; `oracle f : a -> b` declares one that the Lean model takes as a
  parameter, so that the proofs may not rely on its behaviour (e.g. a
  hash-consing order).
- `type_of v` is the sort of the term `v` (`v.ty` in OCaml).
- A language with commutative operators gets the oracle `tag_le` (the
  hash-consing order, compiled to a comparison of the tags in OCaml) and the
  helper `mk_commut_binop` (see [Terms](#terms)).

## Rules

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

| law | rule | rewrite, in `plus (v1 v2)`, `b_and`, `b_not`, `bv_and`, ... |
|---|---|---|
| `[@comm]` | none | the rules match the operands in either order |
| `[@fold f]` | `lits`, `lit` | `Int i1 + Int i2 -> Int (f i1 i2)`, `not (Bool b) -> Bool (f b)` |
| `[@fold f lift]` | `lits`, `lit` | `Int i1 + Int i2 -> lift (f i1 i2)` |
| `[@unit c]` | `unit_zero`, `unit_ones` | `x + 0 -> x`, `x & y -> x` when `y` is `ones` |
| `[@zero c]` | `zero_false` | `x && false -> false` |
| `[@idem]` | `same` | `x && x -> x` |
| `[@invol]` | `not`, after the operator | `not (not x) -> x` |

The rewrites are on whole terms: in `rule b_not : Not v`, the rule of
`[@invol]` is the case `not x -> x`, on the operand `v`.

- `[@comm]` applies to binary operators: see [Terms](#terms) and
  [Proofs](#proofs).
- `[@fold f lift]`: `f : p1 -> ... -> a1 -> a2 -> r` takes the last parameters
  of the node that it has room for (`z_extract from_ to_ z`,
  `add_overflows signed l r`), then the values of the literals (`Int i1`,
  `Int i2`, `Bool b`). Its parameters of type `ty` right before the values
  receive the sorts of the literal operands, in order
  (`fn z_add (s _ : ty) (l r : int) : int`). `lift : r -> t`, a function or a
  node, makes a term of the result of `f`. It is optional: by default, a
  `bool` or an `int` is lifted with the node of its notation, and a value of
  another type with the leaf of one argument of that type
  (`Float (f_add f1 f2)`). A node is built at the sort that its typing gives,
  or else at the sort of the spec.
- `[@unit c]` and `[@zero c]` take a literal, `0`, `1`, `true` or `false`,
  which the rule matches, or a named constant (see [Constants](#constants)),
  which it compares, with `=`, to the constant at the sort of the other
  operand. The rule is named `unit_c` or `zero_c`, after the literal
  (`unit_zero`, `unit_one`, `unit_true`, `unit_false`, `zero_zero`, ...) or the
  constant (`unit_ones`). A literal is resolved as in patterns, at the sort of
  the operands, and its term is its `constant`, if the language declares one,
  or else the node of its notation. On an operator that does not commute, `c`
  is on the right; on one that does, either side.

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
- Patterns match the kind of a term directly: `Int z`, `Add (c, l, r)`.
- `(C x : S args)` builds the node `C x` at the sort `S args`, which its
  typing must allow: a leaf whose sort its arguments do not determine
  (`node BitVec of int : TBitVector n`) is built this way.
- The sort may also be computed: `(C x : e)`, for any expression `e` of type
  `ty` (a variable, a call of a function or of a primitive, or a parenthesised
  expression such as an `if` or a `match`), builds `C x` at the sort `e`:
  `(Tuple vs : TTuple (types_of vs))` (a sort constructor applied to
  arguments, as above), `(Var x : s)` for a parameter `s : ty`,
  `(Field (i, v) : field_ty v i)`. A computed sort is not checked against the
  typing of `C`, which the sort-constructor form checks for an operator (a leaf
  has no operands to check), so it is up to the function to build `C` at a
  sort that its typing allows. In a rule, the Lean spec of the rule is built at
  the sort of the typing of its node, not at the computed sort, and the
  `ocaml-typed` backend does not constrain the tag of the result. A
  constructor-led sort is a sort constructor (`S args`); `(C x : t)` with the
  name of a type `t` is a type annotation.

## Patterns

- The notations of the language (`notation Bool`, `notation Int`) give
  literal patterns, which stand for their nodes: `true` and `false` for
  `Bool true` and `Bool false` (a `bool` notation), the numerals `0`, `1`,
  `-1`, ... for `Int 0`, ... (an `int` one), `#x` and `#_` for `Int x` and
  `Int _` (either), `#x` binding the argument of the node. A literal is
  resolved by its kind (numerals, booleans); if several notations remain, by
  the head of the sort of its position (the operands of a spec, the arguments
  of a node in a pattern, the parameters of helpers annotated with a sort),
  compared with the result sort of each notation's node; otherwise it is an
  error, and the pattern names the node (`Int x`).
- A repeated variable matches equal terms (`=`): `| p, not p -> v_false`.
- The operands of commutative operators match in either order: `x + #k` also
  matches `#k + x`. The swap is left out when both operands are wildcards or
  variables bound nowhere else, as it matches the same terms.
- `p [@comm]` also matches the components of the pair `p` swapped (the
  arguments of the rule function): `(1, ~v) [@comm]` matches both `1, ~v` and
  `~v, 1`.
- Or-patterns, `as`, `when` guards, `Some`/`None`, lists and partial records
  (`{ unsigned = true; _ }`) are supported. Each alternative of an or-pattern is
  tried in turn, together with the guard.

## OCaml

`kanon ocaml-types lang.knl` generates the types of the language, in one
recursive group, with their Kanon names, and its terms:

```ocaml
type t = { kind : kind; ty : ty; tag : int }
```

where `kind` has the leaves and the `Op1`, `Op2`, ... of the operators (see
[Modules, nodes and sorts](#modules-nodes-and-sorts)), and `ty` the sorts.
`node : kind -> ty -> t` hash-conses a term: a table of ephemerons, keyed on
the kind and the sort of the term, gives the term already built, or the new
one, with the next tag. `equal_x` and `hash_x` compare and hash the values of
each type: structurally, terms by their tags, and the abstract types with
their `[@equal]` and `[@hash]`. It only needs Zarith (`int` is `Z.t`). The
table is not safe to use from several OCaml 5 domains at once: a known
limitation.

`kanon ocaml lang.knl` generates the rule functions and helpers, which need
those types in scope: included next to them (`[%%include_file]`, see
[Usage](#usage)), or in the module of `[@@@ocaml_types "Lang_types"]`, which
they open. They call the primitives in the module of
`[@@@ocaml_prims "Lang_prims"]`, which they check against the declarations
(`module _ : sig ... end = Lang_prims`). On terms, `=` compares their tags.

## Typed OCaml

`kanon ocaml-typed lang.knl rules.kn` generates an OCaml interface, `module
type S`, of the smart constructors, where a term `'a t` is typed by a ghost
tag `'a`, a polymorphic variant that says what Kanon knows of it. It is only an
interface: the implementation is written by hand (most often `type 'a t = raw`,
an identity layer), and OCaml checks it against `S`, which has `type raw` and
`type raw_ty` for the untyped terms and sorts, and the escape hatches `untyped`,
`type_`, `cast`, `untype_type` and `type_type`.

```ocaml
[@@@ghost "sint" "[ `NonZero | `Zero ]"]
[@@@ghost "nonzero" "[ `NonZero ]"]
[@@@ghost "sint_ovf" "[ sint | `Overflowed ]"]

sort TBitVec of nat [@ghost sint]
node Add of checked (c) : TBitVec n -> TBitVec n -> TBitVec n
  [@ghost "sint" "sint" "sint_ovf"]
node Div : TBitVec n -> TBitVec n -> TBitVec n
  [@ghost "sint" "nonzero" "sint_ovf"]
```

gives, for the rule functions `bv_add` and `bv_div` of `Add` and `Div`:

```ocaml
val t_bitvec : int -> [> sint ] ty
val bv_add : checked -> [< sint ] t -> [< sint ] t -> [> sint_ovf ] t
val bv_div : [< sint ] t -> [< nonzero ] t -> [> sint_ovf ] t
```

- A `val t_s` per sort, which takes the arguments of the sort (the widths are
  `int`s); a `val` per rule function, named after it, for the node that is its
  spec, and per node with `[@ctor f]` (the leaves, and the nodes that have no
  rule function). Other nodes have none. The parameters of the node are plain
  leading arguments, then come the operands, `[< tag ] t`, and the result,
  `[> tag ] t`. Types of the language are those of `ocaml-types`, opened from
  `[@@@ocaml_types]`, or else in scope. The docs of the rule function or the
  node are carried onto the `val`.
- The tag of a term is that of its sort, `[@ghost tag]` on `sort`, read in the
  typing of the node: `TBool` is `sbool`, declared by the bool module. A sort
  variable (`Eq`, `Ite`, `Distinct`) is shared by the operands and the result,
  as `'a t`. A tag with parameters, `[@@@ghost "'a sseq" "[ `List of 'a ]"]` and
  `sort TSeq of ty [@ghost sseq]`, is applied to the tag of the argument
  of the sort: `[< 'a sseq ] t`. The width, and other values of a sort, are
  erased: Kanon does not check them. A sort with no tag, or a sort that its
  typing does not determine, has any tag, `_ t`.
- The declarations of the tag types are emitted after those that they mention
  (`any` after `sint` and the `sbool` of the bool module, wherever they are
  declared; a type may mention itself, as in `any sseq`); two that mention each
  other are an error.
- A parameter of a node that is a `nat` is an `int`, like the arguments of a
  sort, and an `int` is a `Z.t`. A sort that is a parameter (`ty`) is a `raw_ty`,
  since its tag is not known, and a term that is a parameter and not an operand
  (the body of `Exists of (var * ty) list * t`) is `_ t`: any tag. An `Exists`
  node is therefore `val mk_exists : (var * raw_ty) list -> _ t -> [> sbool ] t`.
- A rule function has a `val` whatever its spec. When the spec is a node over
  the parameters of the function, it is typed as the node. Otherwise it is typed
  by the outermost node of the spec: the result has its tag, a parameter that
  is one of its operands has the tag of that operand, and any other parameter
  has any tag, `_ t`; a spec that is not a node (a call of a function) has any
  tag everywhere. For instance `rule bv_to_bool (v : t) : Not (Eq (v, bv_zero
  (size v)))` is `_ t -> [> sbool ] t`, and `rule bv_lt_zero (v : t) : Lt (true,
  v, bv_zero (size v))` is `[< sint ] t -> [> sbool ] t`. A `[@ghost]` after the
  spec of the rule, `rule bv_to_bool (v : t) : ... [@ghost sint sbool]`, gives
  the tags of its term parameters, then of the result, and replaces the above.
- `[@ghost "t1" ... "tn"]` on a node overrides it with the tags of its operands
  and then of its result (a leaf has one, and an n-ary node two). Such
  refinements, `zero`, `nonzero` or `overflowed` for the integers, are trusted:
  nothing proves them. They are properties of the terms, which a later step
  can prove in Lean (`nonzero v := v <> 0`).
- Not generated: the constraints that bound a variable to a group of tags
  (`([< any ] as 'a) t`, for `compare`), labelled or optional arguments, and
  helpers that are not rule functions.

## Proofs

The site's [guide to proofs](https://n1ark.github.io/kanon/proving.html) walks
through the proof of a language, `examples/ints/`, step by step.

The Lean files are generated in the namespace `R` of `[@@@lean_root]`:

- `Types.lean` and `Syntax.lean` define the types of the language, around
  `R.Abstract` (written by hand): the operators of each arity (`Op1`, `Op2`,
  …, `OpN`), the sorts (`Ty`), the terms (`Term.mk kind ty`, with
  `Kind.Var x`, `Kind.Op2 Op2.And a b`, `Kind.OpN OpN.Distinct l`, …), and
  which operators commute (`Op2.Comm`, from `[@comm]`); `Typing.lean` gives
  the typing of the operators (`Op2.WT op a b t`, over the sorts of the
  operands and of the result; `OpN.WT op e t`, over the sort `e` of all the
  operands).
- `Signatures.lean` checks that `R.Prims` defines the primitives, at their
  types.
- `Model.lean` is a Lean model of the rule functions, over the primitives.
- `Statements.lean` states that every alternative of every rule is sound: its
  result *refines* its spec (the raw term it simplifies), and that the
  operands of every commutative operator commute (`Op2.Plus.comm.Stmt`:
  `Term.mk (Kind.Op2 Op2.Plus a b) t` is refined by
  `Term.mk (Kind.Op2 Op2.Plus b a) t`).
- `Lifts.lean` states that the specs are monotone in their term arguments.
- `Soundness.lean` proves the commutativity of each operator, each rule from
  its alternatives, and every function from its rules, up to `R.opsN_sound`:
  the whole simplifier is sound.

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
  its arms) and `kanon_arm` (on a theorem: the hand-written proof of an arm, or
  of the commutativity of an operator);
- `kanon_proof% X`, the proof of the arm `X` (or of the commutativity
  `Op2.Plus.comm`): its hand-written proof, or the tactic of its function, or
  `kanon_auto`; and the tactic `kanon_arm`, the proof of a rule from those of
  its arms.

The language gives the tactics `kanon_auto` (the default proof of an arm and
of the commutativity of an operator) and `kanon_congr` (refinement by
congruence), which the library declares, with `macro_rules`.

`KanonCore.Proof`, imported on its own, gives the semantic layer and the rule
tactics that the languages share (`soteria`'s `Tiny_values` uses them):

- `Kanon.Sem` (`KanonCore.Sem`): the terms, types, values and environments of
  a language, with `ty`, `WT` and `ev`; `Sem.eval`, `Sem.Refines` and
  `Sem.OLe`, with their generic lemmas (`Sem.Refines.refl`, `trans`, `syn`,
  `sem`, `ev`, `intro`, `intro_eval`, `of_WT`, `of_lift`, `Sem.eval_WT`,
  `Sem.eval_eq_ev`, `Sem.ty_refines`). The language defines `@[reducible] def sem : Kanon.Sem`,
  `abbrev eval := sem.eval`, `abbrev Refines := sem.Refines` and
  `instance : Refinement Refines := Sem.refinement`;
- the tactics `kanon_split`, `kanon_cases`, `kanon_lift`, `kanon_lift_body`,
  `kanon_guards`, `kanon_lits`, `kanon_wt`, `kanon_sem_core`, `kanon_sem`,
  `kanon_close`, `kanon_comm`, `kanon_rule_lift` and `kanon_rule`, and
  `macro_rules` for `kanon_congr`. The language gives them its lemmas by
  attributes (`KanonCore.ProofAttr`): the simp sets `kanon_guards`,
  `kanon_body`, `kanon_lits`, `kanon_wt`, `kanon_ev` and `kanon_val`, the
  possible values of the atoms (`kanon_atom_cases`), and the congruence lemmas
  of its nodes (`kanon_congr_lemma`), and may extend the tactics
  `kanon_congr_pre`, `kanon_congr_side` and `kanon_rule_close`. `kanon_comm`
  (refinement up to the order of the operands of commutative operators, which
  `kanon_rule_lift` tries) uses the congruence lemmas and the commutativity of
  the operators, which `Soundness.lean` tags `kanon_comm_lemma`.
  `kanon_lift` lifts a call `O.f args` with the lemma `R.Lib.lift_f` of
  `Lifts.lean`.

`KanonCore.BoolMod`, imported on its own, proves the rules of the bool module
(`modules/bool.kn`, see [Modules and examples](#modules-and-examples)) once, for
any language that uses it (namespace `Kanon.BoolMod`):

- `BoolMod.Lang S`, for the semantics `S : Kanon.Sem` of a language, is what
  the language gives: the kinds of its terms (`Kind`, with `mk : Kind → Ty →
  Term`, the `Term.mk` of the language), the kinds of the nodes of the module
  (`litK`, `notK`, `andK`, `orK`, `eqK`, `iteK`, `distinctK`) and the type
  `tbool`, such that the terms of the generated statements are definitionally
  equal to them (e.g. `Term.mk (Kind.Op2 Op2.And a b) Ty.TBool` to
  `mk (andK a b) tbool`); its booleans (`vbool : Bool → Val`); the helper
  `sure_neq` (which the modules above extend); and their laws: the typing of
  the nodes (`WT_and`, …), their evaluation by the operations of
  `KanonCore.BoolMod.Val` (`ev_and : ev ρ (mk (andK a b) t) =
  pand vbool (ev ρ a) (ev ρ b)`, …, with `pand`, `por`, `pnot`, `peq`, `pite`
  and `pdistinct`, which the language may use in its own `ev`), that
  well-typed booleans evaluate to booleans (`ev_bool`), that `vbool` is
  injective, and that surely different terms of the same type have different
  values (`sure_neq_sound`). The language defines it as
  `R.boolLang : BoolMod.Lang R.sem` (`R.boolLang x` for the parameters `x` of
  `[@@@lean_param]`), in a module that `R.Proofs` imports;
- `BoolMod.Ops L` is the bool module in the model of the language (its rule
  functions, the oracles `tag_le` and `sort_by_tag`, and the helpers
  `at_most_one`, `distinct_check_one` and `distinct_check`), and
  `BoolMod.Ops.Sound` what the rules assume of them;
- `KanonCore.BoolMod.Rules` proves, for every arm `f.r_rule.arm` of the module
  (with those derived from the laws of `bool.knl` and from the swaps of
  commutative operands), the theorem `Kanon.BoolMod.f.r_rule.arm L B hB`,
  whose statement is that of the arm, for any `L`, `B` and `hB : B.Sound`. Most
  are proved by the tactic `kanon_bool` (`KanonCore.BoolMod.Tactic`).

`Soundness.lean` proves each arm of the module by that theorem, applied to the
language (`fun O hO => BoolMod.f.r_rule.arm boolLang O.bool hO.bool`), the
commutativity of `And`, `Or` and `Eq` by `BoolMod.Lang.refines_and_comm`, …, and
defines the bool module of the model, `Ops.bool O : BoolMod.Ops boolLang`, with
the proof `Ops.Sound.bool : O.Sound → O.bool.Sound` (which uses the field
`sort_by_tag` of the language's `Oracle.Compat`). The arms that the other
modules add to the rule functions of the bool module (`extend rule`) are the
language's, and proved as the others.

An alternative (an arm) is one case of a rule, after expanding its or-patterns
and the swaps of commutative operands; its statement is over the variables of
its pattern, with its guard as a hypothesis (`f.r_name.arm.Stmt`). An arm is
named after the choices that produced it, so that reordering patterns does not
rename it: the head constructor (or operator) of each or-pattern branch taken,
with an index when both branches have the same head (`lt_leq`, `lt1`), and
`swap` for a swap (numbered when there are several), prefixed by `cN` when the
rule has several cases; an arm with no choice is `main`. An alternative that
only swaps commutative operands is proved from the unswapped one, if its guard
and body do not depend on the swaps: by the commutativity of the operators
swapped (`Op2.Plus.comm.ok`), with `kanon_congr` for the operands swapped
below the spec (and for the sort of a spec that is that of an operand,
`type_of v1`, which its typing makes equal to that of the other one, by
`kanon_congr_side`). The proofs to write are thus one per case (when
`kanon_auto` does not find it) and one per commutative operator.

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
  into `kanon`, as the module `use builtin "bool"` uses. The modules above it can add rules to
  its rule functions with `extend rule`, and literals to its helper `sure_neq`
  with `extend fn`. It is the bool module of soteria's
  `Bv_values` and `Tiny_values`.
- `examples/bool/` is a complete example language, made of the bool module
  alone, to start from: `lang.knl` adds its variables to the module, and
  `lean/` is the Lean proof of its rules (the package
  `bool_example`, library `BoolExample`), which uses Kanon's library from this
  repository. Its generated files are committed: `dune test` checks that they
  are up to date (`dune promote` updates them). Its hand-written files are the
  semantics of the language (`Semantics.lean`: values are booleans, poison is
  `none`, and the nodes are evaluated by the operations of
  `KanonCore.BoolMod.Val`), its primitives (`Prims.lean`), the language for
  the bool module (`Bool.lean`: `boolLang`, whose laws are one-line proofs),
  and the congruence of its nodes, for `kanon_congr` (`Lib/Lift.lean`). Its
  rules are those of the bool module, which `KanonCore.BoolMod` proves, so
  `Lib/Rule.lean` and `Proofs.lean` are empty. To check it:

  ```
  cd examples/bool/lean
  lake build
  lake env lean check_axioms.lean  # must not mention sorryAx
  ```

## Language server

`kanon lsp` is a language server (LSP, over standard input and output) for
editors. As files are edited, it checks the whole language they belong to, as
`kanon` does, and reports its errors on the files where they are: all the
errors of the functions of a module once their signatures are known, and of
the independent items of a declaration, rather than only the first.

It knows the names of the language, as Kanon scopes them:

- the global names: functions, primitives, nodes, constructors, types, rules
  (`before r` goes to the rule `r` of the extended function, or to the law that
  derives it, `[@unit 0]`) and operators (`+`, `&&`, `not`, `urem`, ...,
  which go to their `infix` or `prefix` declaration, and whose hover says what
  they build, match and compute);
- the local names: parameters, operands of specs (`v1` in `And (v1, v2)`),
  variables of sorts (`sz` in `(v : TBitVector sz)`, `n` in a typing),
  pattern variables (`x`, `#x`, `p as x`; a variable bound twice, or in each
  alternative of an or-pattern, is bound where it first appears), `let`s and
  the arguments of nodes in their typings.

It gives their definitions; hovers with the header of a definition and the
comment above it, or with what a local is (its type, when the source gives
it) and where it is bound; their references and highlights (of a global, in
the files of the language); their renaming, which refuses operators, keywords,
the names of the built-in modules and invalid new names (a function, a type
or a rule starts with a lowercase letter, a constructor with an uppercase
one); completion of the names of the language; and the symbols of a file and
of the workspace.

A `.kn` file is only meaningful in its language: the server checks a file with
each *root* of the workspace that uses it, the `.knl` files that no other file
uses (e.g. `lang.knl`), as `kanon ocaml lang.knl`; a file that no root uses is
checked with the only root of its directory, or else alone. In Kanon's own
repository, `modules/` stands for the built-in modules, so that they are
checked with the languages that use them. The files of the workspace are found
when it is opened (or a folder added), then from the files the editor opens,
saves and, if it can watch files (`workspace/didChangeWatchedFiles`), creates
and deletes.

Limitations: the names come from the last parse of a file, so a file with a
syntax error only has its global names and operators, found by their text;
rename is then refused. The fields of records are not names. `extend` cases
see the parameters of the function they extend, but not its other locals. A
rule derived from a law has no source, so `before` it goes to the law (and the
checker rejects it, as the derived rules are added after the `extend`s).

## Editors

- `tree-sitter-kanon/` is the [tree-sitter](https://tree-sitter.github.io)
  grammar of `.kn` and `.knl` files, for editors (see its README).
- `editors/zed/` is the [Zed](https://zed.dev) extension: the language
  server above, highlighting, the outline of a file down to the rules of its
  rule functions, brackets, indentation, comments, text objects and snippets.
  Install it with `zed: install dev extension`, from that directory (see its
  README).
