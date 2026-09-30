# Kanon roadmap: from a Bv_values rule language to a value-language framework

Status: proposal. Kanon was `Kanon`, the rule language of soteria's `Bv_values`;
this roadmap was written then, and names files by their paths in soteria.
Implemented so far:
B1 (the language is declared in `.knl` files, such as soteria's
`soteria/lib/bv_values/rules/lang.knl`, with OCaml-style `type` declarations
and `infix`/`prefix` items rather than the syntax sketched below), B2 (the Lean
types, `Types.lean` and `Syntax.lean`, with the Kanon names, and the typing of
the operators, `Typing.lean`, from sort annotations on their constructors;
`Term.WT` remains hand-written), B3 (`Binop.Comm` is generated from `[@comm]`;
`evBinop_comm` remains the hand-written obligation), A1 for the Lean files
(`kanon lean-all` generates them in one run), and A2–A4 (`kanon_tactic` and
`kanon_arm` attributes, and arms named after their choices, with `main` for an
arm without any), and A6 without `Oracle.Compat` (the generated code checks the
types of the primitives, in OCaml with a signature constraint that leaves
`Prims` itself unsealed), and D2 and D3 in OCaml only (tiny_values' smart
constructors are generated from `soteria/lib/tiny_values/rules/`, with no Lean
model), and the front end of modules (§4, question 5: modules declare `node`s
that the language places in its types, add rules to lower modules' functions
with `extend rule` and cases to their helpers with `extend fn`, and declare
their own primitives; Bv_values is made of `bool`, `exists`, `bitvec`, `float`
and `ptr`, and the first two, in `soteria/kanon/modules/`, are shared with
Tiny_values).

Since then, the compiler knows no value language: the values of literals
(`bv`), the variables (`var`), the constants of the laws, the conditional of
`[@distrib_ite]`, the functions that only read the type of a term (`size`), and
the Lean namespace and parameters of the semantics (`FS : FloatSem`) are
declared by the language (see the README), and Kanon lives in its own
repository. The generic Lean core (`KanonCore.Lang`, §C) is here, in `lean/`;
the Lean library of Bv_values and the modules stay in soteria.
§1 describes the state before all of this.

## 1. Where we are

Kanon turns `soteria/lib/bv_values/rules/*.kn` (≈1650 lines, 61 rule
functions, ≈380 rules) into:

- `svalue_rules.gen.ml`, included in `Bv_values.Svalue.Make`;
- `Model.lean`, `Statements.lean`, `Lifts.lean` and `Soundness.lean`, which
  prove `Kanon.opsN_sound` (every smart constructor refines its raw node) with
  the hand-written `Syntax`, `Semantics`, `Prims` and `Lib/` files, plus 47
  hand-written arm proofs.

This works, but only for Bv_values. The Bv_values language is hard-coded in
roughly a dozen places that must be kept in sync by hand:

| What | Where |
|---|---|
| node constructors, data types, argument kinds, Lean names | `syntax.ml` (`constrs`, `data_types`) |
| OCaml paths and types | `gen_ocaml.ml` (`constr_path`, `ocaml_ty`) |
| Lean types | `gen_lean.ml` (`lean_ty`) |
| operator sugar (`+` → `Add`/`bv_add`, `&&` → `And`/`b_and`, …) | `check.ml` (`term_ops`, `node_ops`, `lit_*` table) |
| literal patterns (`#x`, `true`) | `check.ml` (`BitVec`, `Bool`) |
| commutative operators | `check.ml` (`commutative`), `Lib/Cases.lean` (`Binop.Comm`, `evBinop_comm`) |
| term syntax | `Kanon/Syntax.lean`, `svalue_ast.ml` |
| typing, evaluation, sort preservation | `Semantics.lean` (`*.WT`, `evUnop`, `evBinop`), `Lib/Sort.lean` (`obtain` lists), `Lib/Den.lean` |
| primitives | `prelude.kn` `prim` lines, `Svalue.Make.Prims`, `Kanon/Prims.lean`, `Oracle.Compat` |
| which tactic proves which function | `Lib/Rule.lean` (`kanon_proof%` matches on the function *name string*) |
| rule files | `lean/Kanon/dune`, listed four times |

Consequences:

- **tiny_values** cannot use Kanon: its smart constructors (≈350 lines of
  `svalue.ml`) are hand-written and unproved, over a different AST (`Int` of
  `Z.t`, `Plus`/`Minus`/…, `Ite` as its own node).
- **Extensions** cannot use Kanon. `Value_ext.mk` is the hook where an
  extension normalises its nodes, and soteria-rust's `Ext_base` smart
  constructors are hand-written and unproved. The Lean model treats
  `Extension` as opaque (`ρ.ext`), and the rules cannot mention extension
  nodes.
- **Adding a node or operator** means editing `svalue_ast.ml`, `syntax.ml`,
  `Syntax.lean`, `Semantics.lean` (typing and evaluation), `Sort.lean`,
  `Lemmas.lean`, `Den.lean`, the simp sets of `Tactic.lean` and, if the
  operator is commutative, three commutativity lists.
- **Writing and reviewing rules** is harder than it needs to be:
  - About 150 of the ≈380 rules are instances of a few schemas: constant
    folding (`lits:`/`lit:`, ≈48), `default:` fallbacks (58), identities and
    absorbing elements (`same`/`zero`/`one`/`true_`/`false_`, ≈35) and
    distribution over `Ite` (9). Each is written, generated and proved one by
    one.
  - Families such as `upper_bounds`/`lower_bounds`, over `Lt | Leq`, are
    spelled out with or-patterns, which multiplies the arms (for example, 4
    verbatim copies of `b_and.r_eq_extracts` in `Model.lean`).
  - Arm proofs are named by position (`f.r_name.a3.proof`). Reordering an
    or-pattern silently re-targets a hand-written proof onto another arm, and
    a proof whose arm disappeared is silently ignored.
  - When the automation fails, the author gets a Lean goal after the
    `kanon_auto` cascade. That is slow (up to five pipelines per arm) and far
    from the rule's source.
  - There is no fast feedback before Lean: the first signal that a rule is
    wrong is a failed proof or, worse, one that times out.

## 2. Goals

1. **Language-agnostic Kanon.** A value language is *declared*, not hard-coded.
   bv_values, tiny_values and future languages are clients.
2. **Extensible and customisable.** A client can extend a base language with
   its own sorts, nodes and rules (soteria-rust over Bv_values), and can add
   rules to or remove rules from a base rule function, with modular proofs:
   the base is proved once, and each extension only proves what it adds.
3. **More expressive rules.** Common schemas are declared once, and families
   of rules are written once.
4. **Easier to write and review.** Fast feedback while writing, stable proof
   names, local error messages, and a small, explicit trusted base.

**`.kn` files stay short and proof-free.** A rule's label (`same:`) is the
only name an author writes. Everything about proofs lives on the Lean side:
which tactic proves a function, the hand-written arm proofs, and the names of
arms, which are derived from the patterns. The same goes for tests (A5),
which live in their own files. The features added to the language (F) must
make rule files shorter, not longer.

Invariant for every step: `svalue_rules.gen.ml` stays byte-identical unless
the step says otherwise, and `lake build` plus the axiom check stay green. A
reviewer can then check a refactor of the framework by checking that the
generated OCaml did not change.

## 3. Plan

The phases are ordered so that each one is useful on its own and small
enough to review. Phase A needs no design decisions. Phases B and C are the
core of the generalisation. D, E and F build on them, and D can start after
B.

### Phase A: quick wins, with no architectural change

- **A1. One list of rule files.** Keep the `.kn` list once, in
  `lean/Kanon/dune` (a `%{deps}` glob or a single variable), in the fixed
  prelude-first order. `main.ml` gains `--all` to emit every Lean file in one
  run.
- **A2. Proof selection without function names in strings.**
  - Replace the name-string dispatch in `kanon_proof%` with a Lean attribute on
    the generated constants: `attribute [kanon_tactic kanon_cmp] bv_lt bv_leq`,
    in the `Lib/` file that defines `kanon_cmp`.
  - A renamed or deleted function is then a Lean error, not a silent fall
    back to `kanon_auto`, which stays the default.
- **A3. Checked hand-written proofs.**
  - Tag hand-written arm proofs with an attribute
    (`@[kanon_arm b_and.upper_bounds.lt_leq]`) instead of a naming convention.
  - The generator emits a list of every arm, and a Lean check fails on an
    attribute that names no arm.
- **A4. Stable arm names, derived automatically.** Name an alternative by
  the choices that produced it rather than by its index:
  - the branch of each or-pattern, named after its head constructor
    (`Lt ... | Leq ...` gives `lt` and `leq`), with an index only when both
    branches have the same head;
  - whether it is a swap (`.swap`).

  The `.kn` source needs no labels. Reordering then cannot re-target a
  proof. This is a one-off rename of the 47 proofs.
- **A5. Examples and differential testing in OCaml.**
  - Examples in a separate `rules/examples.kn`, for instance
    `b_and (x && true) = x`, compile to an Alcotest suite. The rule files
    themselves do not change.
  - A random-term tester runs next to them. For each rule function it
    generates small well-typed terms (with literals of widths 1–8), builds
    them with the smart constructor and raw, and checks
    `Eval (simplified) = Eval (raw)` under random assignments. It can
    optionally also check Z3 equivalence through `Encoding`.
  - This takes seconds, runs in `dune test`, and catches most wrong rules
    before anyone opens Lean.
  - With per-rule hit counts (see A7), it also reports rules that never fire.
- **A6. Generated primitive signatures.**
  - From the `prim` lines, generate an OCaml module type (`Svalue.Make.Prims`
    is then sealed with it) and a Lean file of `example : <type> := Prims.f`
    checks.
  - A primitive missing on either side, or with the wrong type, then fails
    with a message that names it.
  - `Oracle.Compat` gets the same treatment where it can.
- **A7. Rule catalogue.** Add `kanon doc`, which renders every rule function as
  a table with these columns: rule, pattern, guard, result, comment, and how
  it is proved (auto, which tactic, or hand-written).
  - It is useful for review, and with a `KANON_STATS` build flag that counts
    firings, for profiling (with the `profile-soteria` workflow).

### Phase B: declare the language instead of hard-coding it

Introduce a **language declaration**, a `.knl` file or a `language` section
of `prelude.kn`, that holds everything that is currently a table in the
compiler:

```ocaml
language bv_values

ocaml "Svalue_ast"
lean  "Kanon.Bv"

sort bool, bitvector (n : nat), float (fp : fp), loc (n : nat), pointer (n : nat), ...

data checked = { signed : bool; unsigned : bool }
enum fp = F16 | F32 | F64 | F128

(* literals: how [#x], [true] and [Float f] are matched and built *)
literal BitVec (x : bv) : bitvector (width x)   [@pattern "#x"]
literal Bool (b : bool) : bool                   [@pattern "true" "false"]

node Add (c : checked) (a b : t) : ty a    = bv_add    [@infix "+"] [@comm]
node And (a b : t) : bool                  = b_and     [@infix "&&"] [@comm] [@assoc]
node BvExtract (i j : nat) (v : t) : bitvector (j - i + 1) = bv_extract
node Ite (g : t) (a b : t) : ty a          = b_ite
...
```

Each `node` gives:

- its OCaml and Lean constructor paths;
- its arguments, with `nat` for today's `Small`;
- its result sort;
- its smart constructor;
- its surface sugar;
- its algebraic properties.

`syntax.ml`'s `constrs`, `data_types`, `commutative`, `term_ops`,
`node_ops`, `constr_path`, `ocaml_ty` and `lean_ty` are then all computed
from the declaration, and `check.ml`, `gen_ocaml.ml` and `gen_lean.ml` no
longer mention a single Bv_values name.

Steps:

- **B1. Move the tables** out of `syntax.ml` and `check.ml` into
  `bv_values/rules/lang.knl`, parsed by the existing front end. The generated
  OCaml and Lean are byte-identical, and the diff is a pure move.
- **B2. Generate `Syntax.lean`** (and the `WT` typing predicates, which only
  depend on the declared argument and result sorts) from the declaration. It
  is checked like the other generated files.
- **B3. Generate the commutativity facts.** Generate `Binop.Comm` from
  `[@comm]`. A per-language lemma `op_comm : Comm op → ev op a b = ev op b a`
  remains the only hand-written piece, and the generator emits one
  obligation per `[@comm]` node instead of one list to keep in sync.
- **B4. Check `svalue_ast.ml`**, optionally. Either generate the AST types
  from the declaration, or generate a module that pattern-matches every
  constructor at its declared arity, so that a node missing from either side
  is a compile error. Generating `pp`, `hash` and `iter_vars` and the
  `Eval`/`Encoding` dispatch skeletons is a larger follow-up; see §4, question
  2.
- **B5. Widths as `nat`.** `nat` in Kanon becomes `int` in OCaml (today's
  `Small`) and `Nat` in Lean, with the side condition `0 < n` moved into
  `Ty.WF`. This removes most of the `toNat` plumbing (`kanon_nat_widths`,
  `kanon_fix_widths`, `natCast_toNat_of_pos`, `evalBV_nonpos`). This step
  changes the generated OCaml slightly (fewer `Z.of_int`), so it is its own
  PR, with a benchmark run.

### Phase C: a generic Lean core, and Bv_values as one instance

Split `lean/` into a language-independent core and one directory per
language:

```
lean/Kanon/Core/      -- Sig, Term, eval, Refines, congruence, comm, fuel, Ops
lean/Kanon/Bv/        -- Bv_values: Sig instance, Prims, Den, Lib/, Proofs/, generated files
lean/Kanon/Tiny/      -- tiny_values (phase D)
```

**C1. The signature.** Define a `Sig` structure:

- its sorts, with a value domain per sort;
- its operators;
- the typing of each operator;
- the evaluation of each operator on values: `den : Op → List Val → Option Val`;
- the list of commutative operators, with a proof of commutativity.

The core owns only the nodes that every language shares: variables,
literals, `ite`, `eq`, `not`, `and`, `or`, `distinct` and `exists`.

Recommended design: a generic `Term Sig` whose operator type `Sig.Op` is a
per-language inductive generated from the declaration. `cases`, `decide` and
`simp` then still work on operators. The alternative, keeping one closed
`Kind` per language with the generic lemmas re-generated per language, is
simpler to automate but cannot be summed (see phase E).

**C2. Prove generically, once:**

- sort preservation (`Sort.lean`'s `obtain` lists disappear);
- monotonicity and congruence of `ev` (`Lemmas.lean`, `kanon_congr`);
- `Refines` and its algebra;
- commutation of `[@comm]` operators (`kanon_comm`);
- `Ops`, `Ops.Sound`, `step_sound` over a list of rules, and fuel induction.

`Soundness.lean` then shrinks to one proof term per rule, applied to a
generic `opsN_sound`, instead of two 61-field record literals.

**C3. Language-specific automation.**

- `Den`, `Lit`, `Ovf` and the `kanon_*` tactics move to `Bv/`, unchanged.
- Name-string lookups such as `liftGoal`'s `"Kanon.Lib.lift_" ++ f` and
  `kanon_cases`'s hard-coded atom heads become attribute-driven
  (`@[kanon_lift]`, `@[kanon_atom]`), so a new language registers its own.
- `Lifts.lean` stops being interleaved with `Lib/`: it only depends on
  `Core`, and `Tactic.lean` imports it.

**C4. Spike first.**

- Port the smallest slice first: the Bool rules only (`bool.kn`, ≈90
  rules). Measure `lake build` time and how many arms the automation still
  proves, against today.
- If generic terms make the tactics noticeably slower or weaker, fall back
  to the alternative in C1. Either way, the core lemmas are only written
  once.

### Phase D: tiny_values as a second client

This proves that phases B and C actually generalise.

- **D1. A shared prelude.**
  - Split `prelude.kn` into `core/prelude.kn` (booleans, `ite`, `eq`,
    `mk_commut_binop`, lists) and `bv_values/rules/prelude.kn` (bit-vectors,
    floats, checked flags).
  - Move the Bool rules that do not mention bit-vectors (`b_and`, `b_or`,
    `b_not`, most of `b_ite`, `sem_eq`'s generic cases) to `core/bool.kn`,
    parameterised by hooks for the language-specific cases.
  - Language-specific cases such as `eq_extracts` or `upper_bounds` go in a
    language `extend rule` block (see E2).
- **D2. Declare `tiny_values`.** Sorts `bool` and `int`, with literals
  `Int (z : int)`. Operators `Plus`, `Minus`, `Times`, `Div`, `Rem`, `Mod`,
  `Lt`, `Leq`, `Eq`, `And`, `Or`, `Not`, `Distinct` and `Ite`. Its Lean
  semantics are unbounded integers.
- **D3. Port the rules.** Port the hand-written simplifications of
  `tiny_values/svalue.ml` (constant folding, reassociation, moving
  constants across comparisons, `is_mod`) to `tiny_values/rules/*.kn`, and
  generate `svalue_rules.gen.ml` there.
  - tiny's `Svalue` is not a functor. Its generated code is included in a
    plain `module R`, with its own `Prims`.
  - Keep the cram tests and soteria-linear output identical, as a regression
    check.
- **D4. Prove them.**
  - The tiny rules are almost all linear integer arithmetic, so `omega` and
    `grind` close them.
  - The core proofs (C2) and the shared Bool rules are reused as they are.
  - This is where we learn how much of the proof library is really
    Bv-specific.

### Phase E: extensions and customisation

**E1. Extension languages.** Allow a language to extend another:

```ocaml
language rust_values extends bv_values
sort enum, tuple (n : nat), array (t : ty) (n : nat), ...
node Tuple (vs : t list) : tuple (length vs) = ext_tuple
node PtrMeta (p : t) : ... = ext_ptr_meta
```

- In OCaml, the generated code goes into the `Value_ext.mk` hook. It can call
  the base smart constructors through the `build` callback, and an
  `Ext_prims` module supplies the extension's primitives.
- In Lean, the extension's signature is summed with the base
  (`Sig.sum Bv.Sig Rust.Sig`). This is why C1 needs `Term Sig` to be generic.
- The base's `opsN_sound` is stated for any extension of its signature. The
  base rules never inspect extension nodes, so the existing proofs carry over
  unchanged. `ρ.ext` generalises to "the extension's evaluation".
- The extension proves only its own rules, assuming the base `Ops.Sound`.

**E2. Adding rules to base functions.**
`extend rule b_and with | my_rule: ... before eq_neq` inserts rules into an
existing rule function in a client's rule files.

- The client re-runs Kanon on base plus extension, which is cheap because
  `Svalue.Make` is already instantiated per client. It gets its own
  generated OCaml and its own `Soundness.lean`, which reuses every base arm
  proof and only adds the new ones.
- Soundness still composes, because `step_sound` is a fold over the rule
  list.

**E3. Removing and toggling rules.** Rule groups (`[@group expensive]`) can
be disabled per client at generation time, for example soteria-c without the
float rules, or an analysis that wants fewer rewrites.

- Removing a rule is always sound, so a disabled rule needs no proof work.
  The generator just leaves its `firstSome` entry out.
- This is what makes the rule set customisable for performance tuning.

### Phase F: more expressive rules

Each item is independent. Each one extends the front end, generates the same
per-arm statements as today, and keeps the arm proofs working.

- **F1. Algebraic laws on nodes.**
  - Declare laws on a node: `[@unit 0]`, `[@zero 0]`, `[@idem]`, `[@invol]`,
    `[@fold lit_add]` (constant folding with a primitive), and
    `[@distrib_ite]` (distribute over an `Ite` with a literal operand).
  - The generator derives the corresponding rules and places them first, in
    a fixed order.
  - Each law is proved once per node, as a lemma about `den`, instead of
    once per derived arm. The derived arms are then proved by one generic
    tactic.
  - This removes about 150 hand-written rules, and it removes the `default:`
    case whenever it is the canonical spec (`[@comm]` already implies
    `mk_commut_binop`).
- **F2. Pattern synonyms (views).** For example:

  ```ocaml
  pattern upper (s, a, c) = Lt (s, a, #c) | Leq (s, a, #c)
  ```

  - `upper_bounds: upper (s, a, _) && upper (s, a, _)` then replaces the
    or-pattern.
  - A synonym can carry a computed value
    (`pattern upper (s, a) with bound = ...`), which absorbs `upper_bound`
    and `lower_bound`.
  - Views expand at check time, so the generated code and proofs are
    unchanged.
- **F3. Operator variables.** `(Lt | Leq as op) (s, a, b)` binds `op`, and
  `op (s, b, a)` rebuilds the same node. This removes the rule pairs that
  only differ by operator (`lt`/`leq`, `and_`/`or_` De Morgan, the
  `add`/`sub`/`mul` overflow triples).
- **F4. Freer rule shapes.**
  - Allow `let` before the top-level `match`. Today this is rejected, which
    forces helper functions.
  - Allow labelled nested matches. Each label becomes a rule, with the outer
    pattern and guard as hypotheses.
  - The Lean side already handles `pre` (`split_body`), so this is mostly
    front-end work.
- **F5. AC matching over chains.**
  - Allow `x && ... && not x` for a pattern that searches a flattened chain
    of an `[@assoc] [@comm]` operator, and similarly for `+`, `land` and
    `lor`.
  - This needs a small generic matching primitive, proved once in the core.
  - It is the most expensive item here, so do it last and only if the
    benchmarks show that such rules matter.
- **F6. Loop detection.** The Lean proof is fuel-based, so a rewriting loop
  is sound but hangs OCaml. Add a depth counter in `KANON_STATS` builds, and a
  random-term test (A5) that flags any construction exceeding a bound. This
  is cheaper and more useful than proving termination.

## 4. Open questions for the maintainers

1. **Lean terms (C1).** Should terms be generic over a signature (needed for
   extensions summed with a base, E1), or stay a closed inductive per
   language, with the lemmas generated per language? The recommendation is
   generic terms, gated on the C4 spike.
   *Decided: generic terms, if the C4 spike shows that the automation stays
   as fast and as strong.*
2. **How far the declaration goes (B4).** Should it generate the OCaml AST
   and its boilerplate (`pp`, `hash`, `iter_vars`, and the `Eval`,
   `Encoding` and `Expr.Subst` dispatch)? Doing so removes most of the "add a
   node in 10 places" cost on the OCaml side too, but it touches code outside
   Kanon, which today is hand-tuned for performance.
   *Decided: check only. `svalue_ast.ml` stays hand-written, and a generated
   module checks that it has every declared constructor at its arity.*
3. **The trusted base.** Today the soundness theorem is relative to
   `Semantics.lean`. Nothing checks that `Semantics.lean` agrees with
   `Encoding.ml` (the SMT semantics the solver actually uses) or with
   `Eval.ml`. That is now the largest gap in the argument. A cheap measure
   would be a differential test: evaluate random closed terms with the Lean
   evaluator (`lake exe`), with Z3 through `Encoding` and with `Eval`, and
   compare. Should it be part of phase A?
   *Decided: yes, but after the generic core (C), as `Semantics.lean` will
   move.*
4. **Downstream rules (E2).** Do we want clients to add rules to base
   functions, or only to write rules for their own extension nodes? E2 is
   cheap once C2 exists, but it means that different clients run different,
   separately proved, simplifiers.
   *Decided: no E2. Clients write rules for their own nodes and may disable
   groups of base rules (E3), so that there is one proved base simplifier.*

5. **Composing languages from modules** (decided after the C4 trial, see
   `lean/Kanon/Core/`). Languages are built from modules (Bool at the bottom,
   then BitVec, Int, Float, Ptr, ...), each declared and proved once:
   - In Kanon, each module has its declaration and rules, and a language
     (Bv_values, Tiny_values, soteria-rust's extension) lists its modules.
     The generated OCaml of a language stays over its hand-written AST.
   - In Lean, Kanon generates each language's flat, concrete types, and one
     instance per module (`HasBool L`, ...) whose laws hold by `rfl`. A
     module's rules and proofs are generic over its class.
   - A higher module may add rules to the rule functions of a lower one
     (BitVec adds the bounds rules to Bool's `b_and`), proved once for every
     language that has both; the order of the modules fixes the order of the
     rules. This is inside a language's stack of modules: downstream clients
     still do not extend base rules (question 4).
   - The OCaml of a stack is monolithic: all the rules of its modules are
     merged and generated together, so that soteria-rust gets one value
     instantiation with Bool, BitVec and its own nodes side by side, instead
     of the `Value_ext` functors. Proofs stay modular: a stack that uses a
     module does not re-prove its rules.

## 5. Suggested order of PRs

| # | PR | Changes generated OCaml? |
|---|---|---|
| 1 | A1 + A2 + A3 + A4: rule-file list, tactic attributes, checked proof names, derived arm names | no |
| 2 | A5: examples and random differential tests | no |
| 3 | A6 + A7: primitive signatures, `kanon doc` | no |
| 4 | B1: language declaration, pure move | no |
| 5 | B2 + B3: generated `Syntax.lean`, `WT` and commutativity | no |
| 6 | B5: `nat` widths | slightly |
| 7 | C4 spike, then C1–C3: generic core, `Bv/` instance | no |
| 8 | D1–D4: tiny_values on Kanon | tiny only |
| 9 | F1–F4, one PR each | only where rules are removed |
| 10 | E1–E3 | per client |
| 11 | F5, F6 | depends |

Each PR keeps `dune build`, `dune test`, `lake build` and the axiom check
green.
