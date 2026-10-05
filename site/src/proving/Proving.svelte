<script lang="ts">
  // The guide to proving a language in Lean: the files to write, what Kanon's library gives, and
  // the proof loop, on the worked example examples/ints, whose hand-written files are imported
  // from the repository at build time.
  import { Heading } from "purr";
  import Code from "../components/Code.svelte";
  import DocPage from "../components/DocPage.svelte";

  const sources = import.meta.glob(
    [
      "../../../examples/ints/*.kn",
      "../../../examples/ints/*.knl",
      "../../../examples/ints/lean/*.lean",
      "../../../examples/ints/lean/lakefile.toml",
      "../../../examples/ints/lean/IntsExample/*.lean",
      "../../../examples/ints/lean/IntsExample/Lib/*.lean",
      "../../../examples/division/lean/DivisionExample/Proofs.lean",
    ],
    { query: "?raw", import: "default", eager: true },
  ) as Record<string, string>;

  /** A file of examples/ints, by its path in that directory. */
  function file(path: string): string {
    const text = sources[`../../../examples/ints/${path}`];
    if (text === undefined) throw new Error(`proving: examples/ints/${path} is not imported`);
    return text;
  }

  /** The proofs of examples/division, the example with a subsort. */
  const divisionProofs =
    sources["../../../examples/division/lean/DivisionExample/Proofs.lean"] ?? "";

  const REPO = "https://github.com/N1ark/kanon/tree/main";
</script>

<DocPage page="proving" headings="h2, h3">
  <h1>Proving a language</h1>
  <p class="lede">
    For every rule, Kanon generates a Lean statement that it is sound, and the proof that the whole
    simplifier is sound from the proofs of these statements. This guide is about the rest: the
    files written by hand, what Kanon's Lean library gives them, and how to prove the rules.
  </p>
  <p>
    It follows <a href="{REPO}/examples/ints"><code>examples/ints</code></a>, the language of the
    tutorial's <a href="./#modules">last step</a> (the bool module, a module of integers, and
    variables), proved in <code>examples/ints/lean</code>. Its hand-written files are quoted
    whole: they are templates. <a href="{REPO}/examples/bool"><code>examples/bool</code></a>, the
    bool module alone, is the minimal case.
  </p>
  {#each ["lang.knl", "int.knl", "int.kn"] as name (name)}
    <p class="file"><code>examples/ints/{name}</code></p>
    <Code code={file(name)} />
  {/each}

  <Heading level={2} id="files">The files</Heading>
  <p>
    The Lean files of a language are in the namespace <code>R</code> of
    <code>{`[@@@lean_root "R"]{:kanon}`}</code> (here <code>IntsExample</code>), and in its
    directory of modules. <code>kanon lean-all lang.knl</code> writes the generated ones,
    <code>F.lean</code> to <code>F.lean.gen</code>, in the current directory:
  </p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Types.lean</code>, <code>Syntax.lean</code></td>
        <td>
          The types of the language: <code>Kind</code>, with the leaves and <code>Op1</code>,
          <code>Op2</code>, … of the operators, the sorts <code>Ty</code>, the terms
          <code>{`Term.mk kind ty{:lean}`}</code>, and which operators commute, with the documentation
          comments of the nodes and the sorts.
        </td>
      </tr>
      <tr>
        <td><code>Typing.lean</code></td>
        <td>The typing of the operators: <code>{`Op2.WT op a b t{:lean}`}</code>, over the sorts of the operands and of the result.</td>
      </tr>
      <tr>
        <td><code>Signatures.lean</code></td>
        <td>Checks that <code>R.Prims</code> defines the primitives, at their types.</td>
      </tr>
      <tr>
        <td><code>Model.lean</code></td>
        <td>
          The model of the rule functions: each rule a function to
          <code>{`Option Term{:lean}`}</code>, each rule function the first of its rules that
          applies (<code>firstSome</code>), and <code>Ops</code>, the rule functions, over the
          oracles (<code>Oracle</code>). The documentation comments of the helpers, the oracles and
          the rule functions are carried to it as <code>/-- … -/</code>.
          A helper or a primitive marked <code>{`[@no_lean]{:kanon}`}</code> is not in it (nor in
          any other generated file): it is OCaml only, and no modelled function may call it, so the
          proofs never depend on it.
        </td>
      </tr>
      <tr>
        <td><code>Statements.lean</code></td>
        <td>
          The statement of each arm (<code>f.r_rule.arm.Stmt</code>), and of the commutativity of
          each <code>{`[@comm]{:kanon}`}</code> operator (<code>Op2.Plus.comm.Stmt</code>).
        </td>
      </tr>
      <tr>
        <td><code>Lifts.lean</code></td>
        <td>That the specs are monotone in their term arguments (<code>Lib.lift_f</code>).</td>
      </tr>
      <tr>
        <td><code>Soundness.lean</code></td>
        <td>
          The proof of each arm, of each rule from its arms, of each function from its rules, and
          <code>opsN_sound</code>: the whole simplifier is sound.
        </td>
      </tr>
    </tbody>
  </table>
  <p>The others are written by hand, once per language:</p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr><td><code>Abstract.lean</code></td><td>The Lean types of the abstract types (<code>R.Abstract</code>).</td></tr>
      <tr><td><code>Prims.lean</code></td><td>The primitives (<code>R.Prims</code>).</td></tr>
      <tr>
        <td><code>Semantics.lean</code></td>
        <td>
          The semantics of terms: typing, evaluation, refinement (<code>Refines</code>), and what
          the proofs assume of the oracles (<code>Oracle.Compat</code>).
        </td>
      </tr>
      <tr>
        <td><code>Bool.lean</code></td>
        <td>The language, for the bool module (<code>boolLang</code>), whose rules are then proved by the library.</td>
      </tr>
      <tr><td><code>Lib/Lift.lean</code></td><td>The congruence of refinement, for <code>kanon_congr</code>.</td></tr>
      <tr><td><code>Lib/Rule.lean</code></td><td>The tactics of the proofs of arms, and the lemmas they use.</td></tr>
      <tr><td><code>Proofs.lean</code></td><td>The proofs of the arms that the tactics do not find.</td></tr>
    </tbody>
  </table>

  <Heading level={2} id="library">What the library gives</Heading>
  <p>
    Kanon's Lean library is <code>lean/</code> in its repository: the package <code>kanon</code>,
    the library <code>KanonCore</code>, the namespace <code>Kanon</code>, which the generated files
    open. It has three parts.
  </p>

  <Heading level={3} id="core">KanonCore</Heading>
  <p>What the generated files need, whatever the language:</p>
  <ul>
    <li>
      <code>whenSome</code> and <code>firstSome</code>, with which the model is written, and the
      class <code>{`Refinement R{:lean}`}</code> of refinement relations (reflexive and transitive),
      with <code>Refinement.firstSome_nil</code> and <code>firstSome_cons</code>, from which the
      soundness of a rule function follows from that of its rules;
    </li>
    <li>
      <code>arrayLength</code>, <code>arrayGet</code> and <code>arraySet</code>
      (<code>KanonCore.Array</code>), with which the model uses the arrays of the language (Lean's
      <code>Array</code>), and their lemmas: the length of a set, reading after a set, setting twice,
      the conversions to and from lists;
    </li>
    <li>
      the attributes <code>kanon_spec</code> (the specs <code>f.spec</code>, which the tactics
      unfold), <code>{`kanon_tactic "tac"{:lean}`}</code> (on <code>f.spec</code>: the tactic that
      proves the arms of <code>f</code>) and <code>kanon_arm</code> (on a theorem: the hand-written
      proof of an arm, or of the commutativity of an operator);
    </li>
    <li>
      <code>{`kanon_proof% X{:lean}`}</code>, with which <code>Soundness.lean</code> proves each arm
      <code>X</code>: its <code>kanon_arm</code> proof if there is one, else the
      <code>kanon_tactic</code> of its function, else <code>kanon_auto</code>;
    </li>
    <li>
      the tactics <code>kanon_auto</code> (the default proof of an arm, and of a commutativity) and
      <code>kanon_congr</code> (refinement by congruence), which the language defines with
      <code>macro_rules</code>.
    </li>
  </ul>

  <Heading level={3} id="proof">KanonCore.Proof</Heading>
  <p>The semantics and the tactics that the languages share, imported on their own:</p>
  <ul>
    <li>
      <code>Kanon.Sem</code>, the semantics of a language: its terms, types, values and
      environments, with <code>ty</code>, <code>WT</code> (typing) and <code>ev</code> (evaluation,
      assuming typing). From them, <code>Sem.eval</code> (poison, <code>none</code>, for ill-typed
      terms) and <code>{`Sem.Refines spec r{:lean}`}</code>: <code>r</code> is well-typed, of the
      type of <code>spec</code>, when <code>spec</code> is, and has its value when <code>spec</code>
      has one. With their lemmas (<code>Sem.Refines.refl</code>, <code>trans</code>,
      <code>intro</code>, …) and <code>Sem.refinement</code>, the instance of
      <code>Refinement</code>. The generic lemmas are <code>Sem.Refines.refl</code>,
      <code>trans</code>, <code>syn</code>, <code>sem</code>, <code>ev</code>, <code>intro</code>,
      <code>intro_eval</code>, <code>of_WT</code> and <code>of_lift</code>, and
      <code>Sem.eval_WT</code>, <code>Sem.eval_eq_ev</code> and <code>Sem.ty_refines</code>. The
      language defines <code>{`@[reducible] def sem : Kanon.Sem{:lean}`}</code>,
      <code>{`abbrev eval := sem.eval{:lean}`}</code>,
      <code>{`abbrev Refines := sem.Refines{:lean}`}</code> and
      <code>{`instance : Refinement Refines := Sem.refinement{:lean}`}</code>.
    </li>
    <li>
      The tactics of arms. <code>kanon_rule_lift</code> takes the guard of an arm, unfolds its
      spec, splits the conditionals of its body, lifts its calls to their specs (with the lemmas of
      <code>Lifts.lean</code>), and closes the refinements that are reflexivity or commutativity.
      <code>kanon_rule</code> then proves the typing half of the refinement and splits its value
      half on the values of the atoms, closing what <code>simp_all</code> and <code>omega</code>
      can. They are made of smaller ones, which are also available: <code>kanon_split</code>,
      <code>kanon_cases</code>, <code>kanon_lift</code> (which lifts a call <code>O.f args</code>
      with the lemma <code>R.Lib.lift_f</code> of <code>Lifts.lean</code>),
      <code>kanon_lift_body</code>, <code>kanon_guards</code>, <code>kanon_lits</code>,
      <code>kanon_wt</code>, <code>kanon_sem_core</code>, <code>kanon_sem</code> and
      <code>kanon_close</code>. <code>kanon_comm</code>, which <code>kanon_rule_lift</code> tries,
      proves refinement up to the order of the operands of commutative operators, with the
      congruence lemmas and the commutativity of the operators, which <code>Soundness.lean</code>
      tags <code>kanon_comm_lemma</code>.
    </li>
    <li>
      The language gives these tactics its lemmas by attributes: the simp sets
      <code>kanon_guards</code>, <code>kanon_body</code>, <code>kanon_lits</code>,
      <code>kanon_wt</code>, <code>kanon_ev</code>, <code>kanon_val</code> and
      <code>kanon_close_simp</code>, the values of the atoms (<code>kanon_atom_cases</code>), the
      congruence of its nodes (<code>kanon_congr_lemma</code>), and closing lemmas
      (<code>kanon_close_lemma</code>); and it may extend the tactics
      <code>kanon_congr_pre</code>, <code>kanon_congr_side</code>,
      <code>kanon_rule_close</code> and <code>kanon_close_side</code>.
    </li>
  </ul>

  <Heading level={3} id="boolmod">KanonCore.BoolMod</Heading>
  <p>
    The rules of the bool module, proved once, for any language that uses it (namespace
    <code>Kanon.BoolMod</code>). The arms that other modules add to its rule functions
    (<code>extend rule</code>) are the language's, proved as the others.
  </p>
  <ul>
    <li>
      <code>BoolMod.Lang S</code>, for the semantics <code>S : Kanon.Sem</code> of a language, is
      what the language gives: the kinds of its terms (<code>Kind</code>, with
      <code>mk : Kind → Ty → Term</code>, the <code>Term.mk</code> of the language), the kinds of the
      nodes of the module (<code>litK</code>, <code>notK</code>, <code>andK</code>,
      <code>orK</code>, <code>eqK</code>, <code>iteK</code>, <code>distinctK</code>) and the type
      <code>tbool</code>, such that the terms of the generated statements are definitionally equal
      to them (<code>{`Term.mk (Kind.Op2 Op2.And a b) Ty.TBool{:lean}`}</code> to
      <code>mk (andK a b) tbool</code>); its booleans (<code>vbool : Bool → Val</code>); the helper
      <code>sure_neq</code> (which the modules above extend); and their laws: the typing of the nodes
      (<code>WT_and</code>, …), their evaluation by the operations of
      <code>KanonCore.BoolMod.Val</code> (<code>ev_and</code>, …, with <code>pand</code>,
      <code>por</code>, <code>pnot</code>, <code>peq</code>, <code>pite</code> and
      <code>pdistinct</code>, which the language may use in its own <code>ev</code>), that
      well-typed booleans evaluate to booleans (<code>ev_bool</code>), that <code>vbool</code> is
      injective, and that surely different terms of the same type have different values
      (<code>sure_neq_sound</code>). The language defines it as
      <code>R.boolLang : BoolMod.Lang R.sem</code> (<code>R.boolLang x</code> for the parameters
      <code>x</code> of <code>{`[@@@lean_param]{:kanon}`}</code>), in a module that
      <code>R.Proofs</code> imports.
    </li>
    <li>
      <code>BoolMod.Ops L</code> is the bool module in the model of the language (its rule
      functions, the oracles <code>tag_le</code> and <code>sort_by_tag</code>, and the helpers
      <code>at_most_one</code>, <code>distinct_check_one</code> and <code>distinct_check</code>), and
      <code>BoolMod.Ops.Sound</code> what the rules assume of them.
    </li>
    <li>
      <code>KanonCore.BoolMod.Rules</code> proves, for every arm
      <code>Bool.f.r_rule.arm</code> of the module (with those derived from the laws of
      <code>bool.knl</code> and from the swaps of commutative operands), the theorem
      <code>Kanon.BoolMod.Bool.f.r_rule.arm L B hB</code>, whose statement is that of the arm, for any
      <code>L</code>, <code>B</code> and <code>hB : B.Sound</code>. Most are proved by the tactic
      <code>kanon_bool</code> (<code>KanonCore.BoolMod.Tactic</code>).
    </li>
    <li>
      <code>Soundness.lean</code> proves each arm by that theorem
      (<code>fun O hO => BoolMod.Bool.f.r_rule.arm boolLang O.bool hO.bool</code>), the commutativity
      of <code>And</code>, <code>Or</code> and <code>Eq</code> by
      <code>BoolMod.Lang.refines_and_comm</code>, …, and defines the bool module of the model,
      <code>Ops.bool O : BoolMod.Ops boolLang</code>, with the proof
      <code>Ops.Sound.bool : O.Sound → O.bool.Sound</code> (which uses the field
      <code>sort_by_tag</code> of the language's <code>Oracle.Compat</code>).
    </li>
  </ul>
  <p>
    <code>KanonCore.Lang</code>, in the library, is a trial of a generic core: terms, their
    evaluation and their refinement, for any language.
  </p>

  <Heading level={2} id="steps">Step by step</Heading>

  <Heading level={3} id="project">The project</Heading>
  <p>
    A Lake package that requires Kanon's library, at the toolchain of <code>lean/</code>, with one
    library, the root of the modules (<code>IntsExample.lean</code> imports
    <code>IntsExample.Soundness</code>):
  </p>
  <Code lang="text" code={file("lean/lakefile.toml")} />
  <p>
    The generated files are written by <code>kanon lean-all ../../lang.knl</code>, run in
    <code>IntsExample/</code>, then renamed from <code>F.lean.gen</code> to <code>F.lean</code>
    (in Kanon's repository, a dune rule does it, and <code>dune test</code> checks that they are
    up to date). The modules import each other in this order, the hand-written ones in bold:
  </p>
  <p class="chain">
    <code>Types</code> → <strong><code>Abstract</code></strong> → <code>Syntax</code> →
    <strong><code>Prims</code></strong> → <code>Signatures</code>, <code>Typing</code> →
    <code>Model</code> → <strong><code>Semantics</code></strong> → <code>Statements</code>,
    <strong><code>Bool</code></strong> → <strong><code>Lib/Lift</code></strong> →
    <code>Lifts</code> → <strong><code>Lib/Rule</code></strong> →
    <strong><code>Proofs</code></strong> → <code>Soundness</code>
  </p>
  <p>
    <code>check_axioms.lean</code> checks that the soundness theorem is proved, without
    <code>sorry</code>:
  </p>
  <Code lang="lean" code={file("lean/check_axioms.lean")} />

  <Heading level={3} id="abstract">Abstract.lean</Heading>
  <p>
    The Lean types of the abstract types of the language, in the namespace <code>R</code>, unless
    <code>{`[@lean]{:kanon}`}</code> names an existing type, as here:
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Abstract.lean")} />

  <Heading level={3} id="prims">Prims.lean</Heading>
  <p>
    The primitives that the rules declare with <code>prim</code>, at the types that
    <code>Signatures.lean</code> checks, and <code>ty</code>, the <code>type_of</code> of the rules.
    The oracles (<code>oracle</code>, here the bool module's <code>sort_by_tag</code>, and
    <code>tag_le</code>) are not defined: the model takes them as parameters
    (<code>Oracle</code>).
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Prims.lean")} />

  <Heading level={3} id="semantics">Semantics.lean</Heading>
  <p>
    The meaning of terms, against which the rules are proved: their typing
    (<code>Term.WT</code>, over the generated typing of the operators), their values and
    evaluation (<code>ev</code>, assuming typing), and from them, by the library,
    <code>eval</code> and <code>Refines</code>. The semantics is a <code>Kanon.Sem</code>
    (<code>sem</code>), so that the library's lemmas and tactics apply. The nodes of the bool
    module are evaluated by the operations of <code>KanonCore.BoolMod.Val</code>
    (<code>pand</code>, <code>pite</code>, …), which <code>Bool.lean</code> needs.
    <code>Oracle.Compat</code> is what the proofs assume of the oracles.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Semantics.lean")} />

  <Heading level={3} id="bool">Bool.lean</Heading>
  <p>
    The language, for the bool module: a <code>{`BoolMod.Lang sem{:lean}`}</code>,
    <code>boolLang</code>, the name that <code>Soundness.lean</code> uses. With it, the library
    proves the arms of the bool module for this language. Its fields are the terms of the nodes of
    the module, written as the generated statements write them
    (<code>{`andK a b := .Op2 .And a b{:lean}`}</code>), the booleans, the language's
    <code>sure_neq</code> (extended here with integers), and their laws, mostly unfoldings. The two
    that need a proof are that well-typed booleans evaluate to booleans, from <code>ev_ty</code>,
    and that the terms that <code>sure_neq</code> tells apart have different values.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Bool.lean")} />

  <Heading level={3} id="lift">Lib/Lift.lean</Heading>
  <p>
    The congruence of refinement for each kind of node (<code>Op1</code>, <code>Op2</code>,
    <code>Op3</code>), tagged <code>kanon_congr_lemma</code>. With them, <code>kanon_congr</code>
    proves <code>Lifts.lean</code> (a call of a rule function on terms that refine others refines
    its spec on those), and the arms that swap commutative operands below the spec. The proof is
    the same for every node: refinement keeps the types of the operands, and the operations are
    monotone.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Lib/Lift.lean")} />

  <Heading level={3} id="rule">Lib/Rule.lean</Heading>
  <p>
    The default proof of an arm, <code>kanon_auto</code>, here the library's
    <code>kanon_rule</code>, and the lemmas it uses, by attribute: the typing and evaluation of the
    nodes, the operations on values, the primitives and helpers of the bodies, and the possible
    values of a term, on which it splits.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Lib/Rule.lean")} />

  <Heading level={3} id="proofs">Proofs.lean</Heading>
  <p>
    The proofs of the arms that <code>kanon_auto</code> does not find, tagged
    <code>{`@[kanon_arm]{:lean}`}</code>. Here <code>kanon_auto</code> proves every arm of the
    language's rules (<code>Int.plus</code>, <code>Int.int_lt</code>, the <code>ints</code> rule added to
    <code>Bool.eq</code>) and the commutativity of <code>+</code>, so this file could be empty: its
    proof of the commutativity of <code>+</code> shows how one replaces <code>kanon_auto</code>.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Proofs.lean")} />

  <Heading level={2} id="loop">The proof loop</Heading>
  <ol>
    <li>
      <p>
        <code>lake build</code>. <code>Soundness.lean</code> proves each arm <code>X</code> by
        <code>{`theorem X.ok : X.Stmt := kanon_proof% X{:lean}`}</code>; an arm that its tactic does
        not prove is an error there, which names it. Without <code>Bool.of_bool</code> in
        <code>kanon_body</code>, two arms fail:
      </p>
      <Code
        lang="text"
        code={`error: IntsExample/Soundness.lean:509:59: unsolved goals
⊢ (Bool.of_bool (decide (x✝ = y✝))).WT ∧ (Bool.of_bool (decide (x✝ = y✝))).ty = Ty.TBool
error: IntsExample/Soundness.lean:675:59: unsolved goals`}
      />
      <Code
        lang="lean"
        code={`theorem Bool.eq.r_ints.main.ok : Bool.eq.r_ints.main.Stmt := kanon_proof% Bool.eq.r_ints.main`}
      />
    </li>
    <li>
      <p>
        Read the statement of the arm in <code>Statements.lean</code>: its result refines its
        spec, over the variables of its pattern, with its guard as a hypothesis.
      </p>
      <Code
        lang="lean"
        code={`def Bool.eq.r_ints.main.Stmt : Prop :=
  ∀ (O : Ops), O.Sound →
  ∀ (x : Int) (t__2 : Ty) (y : Int) (t__4 : Ty),
  Refines (Bool.eq.spec (Term.mk (Kind.Int x) t__2) (Term.mk (Kind.Int y) t__4))
  ((Bool.of_bool (decide (x = y))))`}
      />
    </li>
    <li>
      <p>
        Give the tactics the lemma they miss (here, <code>Bool.of_bool</code> in
        <code>kanon_body</code>, as <code>Lib/Rule.lean</code> does), or a function a tactic of its
        own, which its arms try before <code>kanon_auto</code>:
      </p>
      <Code
        lang="lean"
        code={`attribute [kanon_tactic "(intro O hO; simp only [Bool.of_bool]; revert O hO; kanon_rule)"]
  Bool.eq.spec Int.int_lt.spec`}
      />
      <p>
        or prove the arm by hand, in <code>Proofs.lean</code>: an
        <code>{`@[kanon_arm]{:lean}`}</code> theorem of <code>Bool.eq.r_ints.main.Stmt</code>.
      </p>
    </li>
    <li>
      <p>
        Each <code>{`[@comm]{:kanon}`}</code> operator has one statement,
        <code>Op2.Plus.comm.Stmt</code> (<code>{`a + b{:kanon}`}</code> is refined by
        <code>{`b + a{:kanon}`}</code>), proved by <code>kanon_auto</code> or by an
        <code>{`@[kanon_arm]{:lean}`}</code> theorem. From it, and <code>kanon_congr</code> for the
        operands swapped below the spec, Kanon proves the arms that only swap commutative operands
        (<code>swap</code>), if their guard and body do not depend on the swap: the proofs to write
        are at most one per case of a rule, and one per commutative operator.
      </p>
    </li>
    <li>
      <p>Once it builds, check the axioms of the soundness theorem:</p>
      <Code
        lang="text"
        code={`cd examples/ints/lean
lake build
lake env lean check_axioms.lean
# 'IntsExample.opsN_sound' depends on axioms: [propext, Classical.choice, Quot.sound]`}
      />
    </li>
  </ol>

  <Heading level={2} id="subsorts">Subsorts</Heading>
  <p>
    A subsort with a Lean predicate (<code>{`subsort TNonzero : TInt [@lean "Nonzero"]{:kanon}`}</code>)
    asks two things of you.
    <a href="{REPO}/examples/division"><code>examples/division</code></a> is
    a language of integers, with no booleans, that has a division whose divisor is a
    <code>TNonzero</code>, and a node <code>Sq1</code> that returns one.
  </p>
  <ul>
    <li>
      <strong>The predicate</strong>, <code>{`Nonzero : Term → Prop{:lean}`}</code>, which you write in
      <code>Semantics.lean</code>, with the semantics of terms:
      <code>{`def Nonzero (t : Term) : Prop := ∀ ρ z, eval ρ t = some (.int z) → z ≠ 0{:lean}`}</code>.
    </li>
    <li>
      <strong>What it assumes.</strong> A rule function with an operand of the subsort is stated
      for the terms that satisfy it: <code>Nonzero v2 →</code> is a hypothesis of its rules, its
      arms and its step and lifting lemmas, and of <code>Ops.Sound</code>. The proofs that Kanon
      generates thread it, and <code>kanon_auto</code> proves an arm that does not need it. An arm
      that does, like <code>a / a = 1</code> (the quotient by zero is zero), is proved by hand,
      using the hypothesis (<code>hs</code> below): here by a tactic given to its function
      (<code>{`attribute [kanon_tactic "kanon_div_self"] Int.div.spec{:lean}`}</code>), which the
      arms of <code>Int.div</code> try before <code>kanon_auto</code>.
    </li>
    <li>
      <strong>What it proves.</strong> A rule function whose node returns a subsort has to prove
      that what it returns, a rule or its spec, satisfies the predicate:
      <code>sq1.post.main.Stmt</code>. <code>kanon_auto</code> does not prove it, and the build
      fails until a <code>{`@[kanon_arm]{:lean}`}</code> theorem does.
    </li>
    <li>
      <strong>Lifting.</strong> The lifting lemma of a function with a subsort operand assumes the
      predicate of its argument, which <code>kanon_lift</code> cannot discharge: if the body of a
      rule calls such a function, the goal <code>Nonzero v'</code> is left for the hand proof of
      that rule, from what that rule knows of <code>v'</code>. Functions have no sorts, so only
      rules assume or prove anything.
    </li>
    <li>
      <strong>Swaps.</strong> The arms that are derived from another by commutativity are proved as
      the others when there are assumptions, since their operands are other terms than those of the
      arm that they come from. The elements of a list of operands each satisfy the predicate
      (<code>∀ y ∈ vs, Nonzero y</code>).
    </li>
  </ul>
  <Code lang="lean" code={divisionProofs} />
  <p>It is built and checked like the others:</p>
  <Code
    lang="text"
    code={`cd examples/division/lean
lake build
lake env lean check_axioms.lean  # must not mention sorryAx`}
  />

  <Heading level={2} id="pitfalls">Pitfalls</Heading>
  <p>The proof of <code>examples/ints</code> ran into these:</p>
  <ul>
    <li>
      <strong>Typed variables.</strong> With values of several types, a variable must evaluate to a
      value of its sort (<code>{`if v.ty = t then some v else none{:lean}`}</code> in
      <code>ev</code>): <code>BoolMod.Lang.ev_bool</code> needs well-typed booleans to evaluate to
      booleans.
    </li>
    <li>
      <strong>Values of their type.</strong> <code>ev_ty</code>, that well-typed terms evaluate to
      values of their type, is proved by recursion on terms (<code>Bool.lean</code>); the
      <code>ev_bool</code> of <code>boolLang</code> and the typed atom lemmas follow from it.
    </li>
    <li>
      <strong>Nested conjunctions.</strong> The typing laws of <code>BoolMod.Lang</code> are flat
      conjunctions, while the generated <code>Op2.WT</code> nests them:
      <code>{`simp [Term.WT, Op2.WT, and_assoc]{:lean}`}</code>, and <code>grind</code> for
      <code>WT_eq</code> and <code>WT_ite</code>.
    </li>
    <li>
      <strong><code>sure_neq</code>.</strong> Its <code>{`decide (ty a = ty b){:lean}`}</code> does
      not simplify once <code>ty</code> is unfolded: case on <code>{`a.ty = b.ty{:lean}`}</code>
      first (<code>by_cases</code>), then
      <code>{`simp_all [sure_neq, ty, firstSome]{:lean}`}</code>.
    </li>
    <li>
      <strong>Helpers with conditionals.</strong> Put helpers such as <code>Bool.of_bool</code> in
      <code>kanon_body</code>, not <code>kanon_lits</code>, so that <code>kanon_rule_lift</code>
      splits their <code>if</code>s.
    </li>
    <li>
      <strong>The sort of <code>ite</code>.</strong> State its congruence lemma at the sort that the
      spec of <code>Bool.ite</code> writes, <code>{`ty b{:lean}`}</code> (the sort of the first
      branch), so that <code>kanon_congr</code> has no side goal (or give one to
      <code>kanon_congr_side</code>, with <code>macro_rules</code>).
    </li>
    <li>
      <strong>Several types of values.</strong> Give <code>kanon_atom_cases</code> the typed
      lemmas (<code>ev_int</code>, <code>ev_bool</code>, from <code>ev_ty</code>) before the
      untyped one (<code>ev_opt</code>): it uses the first whose hypotheses hold.
    </li>
  </ul>

  <Heading level={2} id="minimal">The minimal case</Heading>
  <p>
    <a href="{REPO}/examples/bool"><code>examples/bool</code></a> is the bool module alone, with
    booleans as values. Its rules are all the bool module's, which the library proves: it has no
    <code>kanon_auto</code>, its <code>Lib/Rule.lean</code> and <code>Proofs.lean</code> are empty,
    and its hand-written files are its semantics, its primitives, its <code>boolLang</code>, whose
    laws are one-line proofs, and the congruence of its nodes. It is the template for a language
    that starts from the bool module.
  </p>
</DocPage>

<style>
  .lede {
    font-size: 1.1em;
    color: var(--color2);
  }
  .chain {
    line-height: 2;
  }
  .file {
    margin-bottom: 0;
    font-size: var(--fs-sm);
    color: var(--color2);
  }
</style>
