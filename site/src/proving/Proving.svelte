<script lang="ts">
  // The guide to proving a language in Lean: the files to write, what Kanon's library gives, and
  // the proof loop, on the worked example examples/ints (a language, and a module proved once),
  // whose hand-written files are imported from the repository at build time.
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
      "../../../examples/ints/lean/IntMod/*.lean",
      "../../../examples/ints/lean/IntMod/Lib/*.lean",
      "../../../examples/ints/lean/IntMod/Proofs/*.lean",
      "../../../examples/ints/lean/IntsExample/Model/Int/plus.lean",
      "../../../examples/division/lean/DivMod/Proofs/**/*.lean",
      "../../../examples/division/lean/DivisionExample/Proofs/**/*.lean",
    ],
    { query: "?raw", import: "default", eager: true },
  ) as Record<string, string>;

  /** A file of examples/ints, by its path in that directory. */
  function file(path: string): string {
    const text = sources[`../../../examples/ints/${path}`];
    if (text === undefined) throw new Error(`proving: examples/ints/${path} is not imported`);
    return text;
  }

  /** The hand-written proofs of examples/division, the example with a subsort. */
  const divisionProofs = ["DivMod/Proofs/Int/div.lean", "DivisionExample/Proofs/Int/sq1.lean"].map(
    (name) => [name, sources[`../../../examples/division/lean/${name}`] ?? ""],
  );

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
    variables), proved in <code>examples/ints/lean</code>: its modules once, for any language that
    uses them, and the language as an instance of them. Its hand-written files are quoted
    whole: they are templates. <a href="{REPO}/examples/bool"><code>examples/bool</code></a>, the
    bool module alone, is the minimal case, and
    <a href="{REPO}/examples/two_langs"><code>examples/two_langs</code></a> two languages that
    share a module proved once, one of which adds a node and a module of its own.
  </p>
  {#each ["lang.knl", "int.knl", "int.kn"] as name (name)}
    <p class="file"><code>examples/ints/{name}</code></p>
    <Code code={file(name)} />
  {/each}

  <Heading level={2} id="files">The files</Heading>
  <p>
    The Lean files of a language are in the namespace <code>R</code> of
    <code>{`[@@@lean_root "R"]{:kanon}`}</code> (here <code>IntsExample</code>), and in its
    directory of modules. A module whose <code>.knl</code> has
    <code>{`[@@@lean_module "M"]{:kanon}`}</code> (here <code>int.knl</code>, <code>IntMod</code>) is
    proved once, in the namespace <code>M</code>, for every language that uses it (see
    <a href="#modules">Modules proved once</a>); the others are proved with the language.
    <code>kanon lean-all DIR lang.knl</code> writes the generated files under <code>DIR/R</code>
    and <code>DIR/M</code>, one file per rule function where they are many (in the directory of its
    module: <code>Model/Int/plus.lean</code> for <code>Int.plus</code>), each importing only what it
    uses, so that changing a rule only rebuilds the files of its function and the two that put them
    together, <code>Model.lean</code> and <code>Soundness.lean</code>. Those of the language:
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
        <td><code>Ops.lean</code>, <code>Model/M/f.lean</code>, <code>Model.lean</code></td>
        <td>
          The model of the rule functions: <code>Ops.lean</code> has the record of the rule
          functions and their specs, each <code>Model/M/f.lean</code> a helper (or a group of
          mutually recursive ones) or the rules of a rule function, and <code>Model.lean</code>
          the rule functions with fuel (<code>opsN</code>). Each rule a function to
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
        <td><code>Statements.lean</code>, <code>Statements/M/f.lean</code></td>
        <td>
          That the rule functions refine their specs (<code>Ops.Sound</code>), the commutativity of
          each <code>{`[@comm]{:kanon}`}</code> operator (<code>Op2.Plus.comm.Stmt</code>), and for
          each rule function the statement of each arm (<code>f.r_rule.arm.Stmt</code>).
        </td>
      </tr>
      <tr>
        <td><code>Interface.lean</code>, <code>Instance.lean</code></td>
        <td>
          The language as an instance of the modules proved once that it uses:
          <code>modSyntax</code>, their interfaces (<code>KanonBool.Syntax</code>,
          <code>IntMod.Syntax</code>) for its terms, whose laws hold by definition, and
          <code>ModSem</code>, what they need of its semantics; then the instances of their
          <code>Sem</code> classes (from <code>lang</code>, in <code>Lang.lean</code>) and the
          model of the language for each (<code>Ops.toInt O : IntMod.Ops modSyntax.toIntSyntax</code>,
          with <code>Ops.Sound.toInt</code>).
        </td>
      </tr>
      <tr>
        <td><code>Lifts.lean</code>, <code>Nodes.lean</code></td>
        <td>
          For the arms that the language proves itself only: that the specs are monotone in their
          term arguments (<code>Lib.lift_f</code>), and the typing and the evaluation of each node
          in terms of those of its operands (<code>Nodes.Op2.Plus.ev</code>), for the tactics (the
          simp sets <code>kanon_node_wt</code> and <code>kanon_node_ev</code>, which they rewrite
          with before <code>kanon_wt</code> and <code>kanon_ev</code>).
        </td>
      </tr>
      <tr>
        <td><code>Soundness/Laws.lean</code>, <code>Soundness/M/f.lean</code>, <code>Soundness.lean</code></td>
        <td>
          The proof of the commutativity of the operators, then for each rule function the proof
          of each arm (each with its own bound on heartbeats, see
          <a href="reference.html#floating"><code>{`[@@@lean_heartbeats]{:kanon}`}</code></a>), of
          each rule from its arms and of the function from its rules, and
          <code>opsN_sound</code>: the whole simplifier is sound. An arm of a module proved once is
          its theorem, applied to the language
          (<code>{`fun O hO => IntMod.….ok (S := sem) modSyntax.toIntSyntax (Ops.toInt O) (Ops.Sound.toInt hO){:lean}`}</code>).
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
        <td><code>Lang.lean</code></td>
        <td>
          What the modules proved once need of the semantics (<code>lang : ModSem sem modSyntax</code>):
          its values, and the laws that do not hold by definition.
        </td>
      </tr>
      <tr>
        <td><code>Lib/Lift.lean</code>, <code>Lib/Rule.lean</code>, <code>Proofs/</code></td>
        <td>
          Only if the language proves arms itself (see <a href="#closed">Proving with the
          language</a>): the congruence of refinement, the tactics of the proofs of arms, and the
          proofs that the tactics do not find.
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={2} id="modules">Modules proved once</Heading>
  <p>
    A module with <code>{`[@@@lean_module "M"]{:kanon}`}</code> is proved in the namespace
    <code>M</code>, over an interface: an abstract language with its nodes, of which any language
    that uses the module is an instance. Its proofs are built once, and a change to a language (a
    node, a module, a rule of its own) does not rebuild them. Its files are under
    <code>DIR/M</code>, the generated ones:
  </p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Syntax.lean</code></td>
        <td>
          <code>{`structure Syntax (S : Kanon.Sem) [DecidableEq S.Term] [DecidableEq S.Ty]{:lean}`}</code>,
          the interface, which extends those of the modules it uses
          (<code>toBoolSyntax : KanonBool.Syntax S</code>), or <code>Kanon.Base S</code> (the
          kinds of terms, <code>Kind</code>, and <code>{`node : Kind → S.Ty → S.Term{:lean}`}</code>):
          its sorts (<code>TInt</code>) with their disjointness (<code>TInt_ne_TBool</code>), the
          kinds of its nodes (<code>PlusK</code>), their typing (<code>WT_Plus</code>), a matcher
          for each node (<code>asPlus</code>, with <code>asPlus_node</code> and
          <code>asPlus_sound</code>), the predicates of its subsorts, its primitives, and its
          helpers, each with the law of its body (<code>int_add_eq</code> for the primitive <code>int_add</code>; <code>bool_of_bool_eq</code> in <code>KanonBool.Syntax</code>).
        </td>
      </tr>
      <tr>
        <td><code>Ops.lean</code></td>
        <td>
          The specs of its rule functions over the interface (<code>{`Int.plus.spec L a b{:lean}`}</code>),
          <code>{`Ops L{:lean}`}</code>, the rule functions and the oracles that its rules call (with
          those of the modules it uses), and <code>Ops.Sound</code>.
        </td>
      </tr>
      <tr>
        <td><code>Statements.lean</code>, <code>Statements/M/f.lean</code></td>
        <td>
          The statements of its arms and of its commutativities, for every interface:
          <code>{`∀ {S} … (L : Syntax S) [Sem L] (O : Ops L), O.Sound → …{:lean}`}</code>.
        </td>
      </tr>
      <tr>
        <td><code>Lifts.lean</code>, <code>Soundness/Laws.lean</code>, <code>Soundness/M/f.lean</code></td>
        <td>
          The monotonicity of its specs, and the proofs of its arms, by
          <code>{`kanon_proof% X{:lean}`}</code>, as a language's.
        </td>
      </tr>
    </tbody>
  </table>
  <p>And the hand-written ones:</p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Sem.lean</code></td>
        <td>
          <code>{`class Sem (L : Syntax S){:lean}`}</code>, what the proofs need of the semantics of a
          language, extending those of the modules it uses (as
          <code>{`toBoolSem : KanonBool.Sem L.toBoolSyntax{:lean}`}</code>): its values and the
          evaluation of its nodes. Its laws default to <code>kanon_law</code>, which proves them for
          a language whose definitions they unfold to. With <code>Oracle.Compat</code>, what the
          proofs assume of its oracles, if it has some.
        </td>
      </tr>
      <tr><td><code>Lib/Lift.lean</code></td><td>The congruence of refinement for its nodes, for <code>kanon_congr</code>.</td></tr>
      <tr><td><code>Lib/Rule.lean</code></td><td>The tactics of the proofs of its arms (<code>kanon_auto</code>).</td></tr>
      <tr><td><code>Proofs/M/f.lean</code>, <code>Proofs/Laws.lean</code></td><td>The proofs that the tactics do not find.</td></tr>
    </tbody>
  </table>
  <p>
    The arms that a module adds to the rules of another (<code>extend rule</code>) are proved with
    the module that adds them. A helper of a module proved once that other modules extend
    (<code>extend fn</code>) is marked <code>{`[@extensible]{:kanon}`}</code>, as the bool module's
    <code>sure_neq</code>: it is a field of the interface without the law of its body, and its
    <code>Sem</code> class states what the proofs need of it
    (<code>KanonBool.Sem.sure_neq_sound</code>), which each language proves.
  </p>
  <p>
    A language that uses such modules has its sorts, nodes and helpers as their fields, by
    definition. <code>Interface.lean</code> proves their laws: those of the nodes by
    <code>rfl</code> or <code>kanon_law</code>, those of the matchers by cases, and those of the
    helpers by <code>kanon_bridge</code>, which unfolds the helper of the language and splits the
    cases of its <code>match</code> (on the nodes of the language, and its catch-all) against those
    of the module's. The parents of a <code>Sem</code> class are named <code>to</code> and the name
    of their module (<code>toBoolSem</code>), and the <code>Oracle.Compat</code> of a language
    has a field for each module proved once whose rules call oracles, named after it in lowercase
    (<code>{`bool : KanonBool.Oracle.Compat orc.sort_by_tag{:lean}`}</code>).
  </p>

  <Heading level={3} id="closed">Proving with the language</Heading>
  <p>
    A module without <code>{`[@@@lean_module]{:kanon}`}</code> is proved with each language that
    uses it, over its terms (as <code>examples/arrays</code>), and so is a rule function of a module
    proved once that is marked <code>{`[@lean_closed]{:kanon}`}</code> (as <code>Num.max</code> in
    <code>examples/two_langs</code>), and the postconditions of the rule functions that return a
    subsort. The language then writes <code>Lib/Lift.lean</code>, <code>Lib/Rule.lean</code> and
    its <code>Proofs/</code>, as a module does, over its own terms, and Kanon generates
    <code>Lifts.lean</code> and <code>Nodes.lean</code>. It is the way out when a proof is easier
    over the terms of one language, or when the interface does not fit: the interfaces of a module
    and of the modules it uses must form a chain (a module that uses two modules that do not use
    each other gets the fields of the second as its own, which its lemmas do not match).
  </p>

  <Heading level={2} id="library">What the library gives</Heading>
  <p>
    Kanon's Lean library is <code>lean/</code> in its repository: the package <code>kanon</code>,
    with the libraries <code>KanonCore</code>, the namespace <code>Kanon</code>, which the
    generated files open, and <code>KanonBool</code>, the bool module.
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
      proves the arms of <code>f</code>; on <code>Syntax</code>, that of the arms a module adds to
      the rules of another) and <code>kanon_arm</code> (on a theorem: the hand-written
      proof of an arm, or of the commutativity of an operator);
    </li>
    <li>
      <code>{`kanon_proof% X{:lean}`}</code>, with which <code>Soundness/M/f.lean</code> proves each arm
      <code>X</code>: its <code>kanon_arm</code> proof if there is one, else the
      <code>kanon_tactic</code> of its function, else <code>kanon_auto</code>;
    </li>
    <li>
      the tactics <code>kanon_auto</code> (the default proof of an arm, and of a commutativity) and
      <code>kanon_congr</code> (refinement by congruence), which the language or the module defines
      with <code>macro_rules</code>;
    </li>
    <li>
      the command <code>kanon_node_lemma</code> (<code>KanonCore.Node</code>), with which
      <code>Nodes.lean</code> states the lemmas of the nodes, in the simp sets
      <code>kanon_node_wt</code> and <code>kanon_node_ev</code>: the typing or the evaluation of a
      node, with the definitions applied to the node or to its parts unfolded;
    </li>
    <li>
      <code>KanonCore.Generic</code>, for the modules proved once: <code>Kanon.Base</code> and
      <code>Kanon.OpsBase</code> (the oracle <code>tag_le</code>), the roots of the interfaces and
      of their models, the simp set and tactic <code>kanon_law</code>, which proves a law by
      unfolding the definitions of a language (tag a lemma <code>kanon_law</code> for it to use it),
      and <code>{`kanon_bridge f{:lean}`}</code>, which proves the law of a helper.
    </li>
  </ul>
  <p>
    <code>KanonCore.Model</code>, the part of it that the model needs (<code>whenSome</code>,
    <code>firstSome</code> and the arrays), is what <code>Prims.lean</code> imports: the model is
    then built without Lean's meta-programming library, which every other module imports, and
    which takes a second to load.
  </p>

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
      with the lemma <code>Lib.lift_f</code> of <code>Lifts.lean</code>),
      <code>kanon_lift_body</code>, <code>kanon_guards</code>, <code>kanon_lits</code>,
      <code>kanon_wt</code>, <code>kanon_sem_core</code>, <code>kanon_sem</code>,
      <code>kanon_close</code>, <code>kanon_refl</code> and
      <code>{`kanon_on_refines tac{:lean}`}</code> (which runs <code>tac</code> on the goal if it is
      a refinement). <code>kanon_refl</code>, <code>kanon_congr</code> and <code>kanon_comm</code>
      match the terms, and their lemmas, up to reducible definitions only, so that on different
      terms they fail without evaluating them: state the congruence and commutativity lemmas over
      the terms as the specs write them. <code>kanon_comm</code>, which <code>kanon_rule_lift</code> tries,
      proves refinement up to the order of the operands of commutative operators, with the
      congruence lemmas and the commutativity of the operators, which
      <code>Soundness/Laws.lean</code> tags <code>kanon_comm_lemma</code>.
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

  <Heading level={3} id="kanonbool">KanonBool</Heading>
  <p>
    The bool module (<code>modules/bool.knl</code> has
    <code>{`[@@@lean_module "KanonBool"]{:kanon}`}</code>), proved once, as any module: its
    generated files, and its <code>Sem.lean</code> (<code>KanonBool.Sem</code>: the booleans
    <code>vbool</code>, the evaluation of its nodes by the operations of
    <code>KanonBool.Val</code>, <code>pand</code>, <code>por</code>, <code>pnot</code>,
    <code>peq</code>, <code>pite</code> and <code>pdistinct</code>, which a language uses in its
    own <code>ev</code>, that well-typed booleans evaluate to booleans, <code>ev_bool</code>, and
    that the terms that <code>sure_neq</code> tells apart have different values,
    <code>sure_neq_sound</code>), its congruence lemmas (<code>Lib/Lift.lean</code>) and its
    tactic, <code>kanon_bool</code> (<code>Lib/Rule.lean</code>), which other modules may use.
    A language does not generate its files: they are in the library.
  </p>

  <Heading level={2} id="steps">Step by step</Heading>

  <Heading level={3} id="project">The project</Heading>
  <p>
    A Lake package that requires Kanon's library, at the toolchain of <code>lean/</code>, with a
    library for the language, the root of its modules (<code>IntsExample.lean</code> imports
    <code>IntsExample.Soundness</code>), and one for each module proved once:
  </p>
  <Code lang="text" code={file("lean/lakefile.toml")} />
  <p>
    The generated files are written by <code>kanon lean-all . ../lang.knl</code>, run in
    <code>examples/ints/lean</code> (in Kanon's repository, <code>dune test</code> runs
    <code>kanon lean-all --check</code>, which checks that they are up to date). The modules of the
    language import each other in this order, the hand-written ones in bold:
  </p>
  <p class="chain">
    <code>Types</code> → <strong><code>Abstract</code></strong> → <code>Syntax</code> →
    <strong><code>Prims</code></strong> → <code>Signatures</code>, <code>Typing</code> →
    <code>Ops</code> → <code>Model/M/f</code> → <code>Model</code>;
    <code>Ops</code> → <strong><code>Semantics</code></strong> → <code>Statements</code> →
    <code>Interface</code> → <strong><code>Lang</code></strong> → <code>Instance</code> →
    <code>Soundness/Laws</code>; <code>Statements</code>, <code>Model/M/f</code> →
    <code>Statements/M/f</code> → <code>Soundness/M/f</code> → <code>Soundness</code>
  </p>
  <p>And those of the int module:</p>
  <p class="chain">
    <code>Syntax</code> → <strong><code>Sem</code></strong> → <code>Ops</code> →
    <code>Statements</code> → <strong><code>Lib/Lift</code></strong> → <code>Lifts</code> →
    <strong><code>Lib/Rule</code></strong> → <code>Soundness/Laws</code>;
    <code>Statements</code> → <code>Statements/M/f</code> → <strong><code>Proofs/M/f</code></strong>
    → <code>Soundness/M/f</code>
  </p>
  <p>
    A hand-written module imports only what it uses, as the generated ones do: the models of the
    helpers it mentions (<code>Lang.lean</code> imports <code>Model/Bool/sure_neq</code>), and a
    proof of the arms of <code>M.f</code> the statements of <code>M.f</code>. Importing all of the
    model (<code>Model</code>) would rebuild them, and everything after them, whenever a rule
    changes. The model of <code>Int.plus</code>, for instance:
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Model/Int/plus.lean")} />
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
    (<code>sem</code>), so that the library's lemmas and tactics apply. The nodes of the modules
    are evaluated by their operations (<code>KanonBool.pand</code>, <code>IntMod.addV</code>, …),
    so that the laws of their <code>Sem</code> classes hold by definition.
    <code>Oracle.Compat</code> is what the proofs assume of the oracles: here, what the bool module
    assumes.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Semantics.lean")} />

  <Heading level={3} id="lang">Lang.lean</Heading>
  <p>
    The language, for its modules: <code>lang</code>, a <code>{`ModSem sem modSyntax{:lean}`}</code>
    (the name that <code>Instance.lean</code> uses). Its fields are the values that the modules
    need (the booleans, the integers and how to read them back) and the laws of their
    <code>Sem</code> classes, which are mostly proved by default. The two that need a proof here are
    that well-typed booleans evaluate to booleans, from <code>ev_ty</code>, and that the terms
    that <code>sure_neq</code> (extended by the int module) tells apart have different values.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Lang.lean")} />

  <Heading level={3} id="sem">IntMod/Sem.lean</Heading>
  <p>
    What the int module needs of a language, over its interface: the integer values, the
    operations that evaluate its nodes, and their laws. The operations are those of any language
    whose values have integers, so that a language evaluates the nodes with them.
  </p>
  <Code lang="lean" code={file("lean/IntMod/Sem.lean")} />

  <Heading level={3} id="lift">IntMod/Lib/Lift.lean</Heading>
  <p>
    The congruence of refinement for each node of the module, tagged
    <code>kanon_congr_lemma</code>. With them, <code>kanon_congr</code> proves
    <code>Lifts.lean</code> (a call of a rule function on terms that refine others refines its spec
    on those), and the arms that swap commutative operands below the spec. The proof is the same
    for every node: refinement keeps the types of the operands, and the operations are monotone.
  </p>
  <Code lang="lean" code={file("lean/IntMod/Lib/Lift.lean")} />

  <Heading level={3} id="rule">IntMod/Lib/Rule.lean</Heading>
  <p>
    The default proof of an arm, <code>kanon_auto</code>: here a tactic of the module,
    <code>kanon_int</code>, which unfolds the laws of the interface and of the <code>Sem</code>
    classes, and splits on the values of the operands, as <code>kanon_rule</code> does for a
    language. A language that proves arms itself uses <code>kanon_rule</code>, given its lemmas by
    attribute (the typing and evaluation of the nodes, the operations on values, the primitives and
    helpers of the bodies, and the possible values of a term, on which it splits), as
    <code>examples/arrays</code> does.
  </p>
  <Code lang="lean" code={file("lean/IntMod/Lib/Rule.lean")} />

  <Heading level={3} id="proofs">Proofs/</Heading>
  <p>
    The proofs of the arms that <code>kanon_auto</code> does not find, tagged
    <code>{`@[kanon_arm]{:lean}`}</code>, in <code>Proofs/M/f.lean</code> for the arms of the rule
    function <code>M.f</code>, and in <code>Proofs/Laws.lean</code> for the commutativity of the
    operators. A file there is optional, and written by hand only: <code>kanon lean-all</code>
    makes the generated proofs of <code>M.f</code> (<code>Soundness/M/f.lean</code>) import it when
    it exists, and its <code>{`@[kanon_arm]{:lean}`}</code> theorems then replace the default
    proofs of their arms, by name. It imports the statements it proves
    (<code>Statements/M/f</code>, or <code>Statements</code>) and what its proofs use, and is
    rebuilt only when they change. Here <code>kanon_auto</code> proves every arm of the module's
    rules (<code>Int.plus</code>, <code>Int.int_lt</code>, the <code>ints</code> rule added to
    <code>Bool.eq</code>), and <code>Proofs/Laws.lean</code> proves the commutativity of
    <code>+</code>, for any language. Run <code>kanon lean-all</code> after adding or removing one.
  </p>
  <Code lang="lean" code={file("lean/IntMod/Proofs/Laws.lean")} />

  <Heading level={2} id="loop">The proof loop</Heading>
  <ol>
    <li>
      <p>
        <code>lake build</code>. <code>Soundness/M/f.lean</code> proves each arm <code>X</code> of
        <code>M.f</code> by
        <code>{`theorem X.ok : X.Stmt := kanon_proof% X{:lean}`}</code>; an arm that its tactic does
        not prove is an error there, which names it (or exceeds its heartbeats, and fails then).
        Without <code>bool_of_bool_eq</code> in <code>kanon_int</code>, two arms fail (the
        tactic stops partway, at a step that names a hypothesis it did not get to):
      </p>
      <Code
        lang="text"
        code={`error: IntMod/Soundness/Int/int_lt.lean:16:23: Unknown identifier \`e\`
error: IntMod/Soundness/Bool/eq.lean:16:23: Unknown identifier \`e\``}
      />
      <Code
        lang="lean"
        code={`theorem Bool.eq.r_ints.main.ok : Bool.eq.r_ints.main.Stmt :=
  no_implicit_lambda% (kanon_proof% Bool.eq.r_ints.main)`}
      />
    </li>
    <li>
      <p>
        Read the statement of the arm in <code>Statements/Bool/eq.lean</code>: for any language
        <code>L</code>, its result refines its spec, over the variables of its pattern, with its
        guard as a hypothesis.
      </p>
      <Code
        lang="lean"
        code={`def Bool.eq.r_ints.main.Stmt : Prop :=
  ∀ {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] (L : Syntax S) [Sem L] (O : Ops L), O.Sound →
  ∀ (x : Int) (t__2 : S.Ty) (y : Int) (t__4 : S.Ty),
  S.Refines (KanonBool.Bool.eq.spec L.toBoolSyntax (L.node (L.IntK x) t__2) (L.node (L.IntK y) t__4))
  ((L.bool_of_bool (decide (x = y))))`}
      />
    </li>
    <li>
      <p>
        Give the tactics the lemma they miss (here, <code>bool_of_bool_eq</code>, the law of
        the helper <code>Bool.of_bool</code>, as <code>Lib/Rule.lean</code> does), or a function a
        tactic of its own, which its arms try before <code>kanon_auto</code>:
      </p>
      <Code
        lang="lean"
        code={`attribute [kanon_tactic "kanon_int"] Int.plus.spec Int.int_lt.spec Syntax`}
      />
      <p>
        (on <code>Syntax</code>, the module's interface: the tactic of the arms that the module
        adds to the rules of another, such as <code>Bool.eq.r_ints</code>),
        or prove the arm by hand, in <code>Proofs/Bool/eq.lean</code> (then run
        <code>kanon lean-all</code>, so that <code>Soundness/Bool/eq.lean</code> imports it): an
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
        (<code>swap</code>), if their guard and body do not depend on the swap (other than through
        the sorts of the swapped terms, or by building raw nodes of them): the proofs to write
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
      In a module proved once, it is a field of the interface (<code>L.Nonzero</code>), and its
      <code>Sem</code> class states what the proofs need of it.
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
      <code>sq1.post.main.Stmt</code>. It is proved with each language, over its terms (in
      <code>DivisionExample/Proofs</code>): <code>kanon_auto</code> does not prove it, and the build
      fails until a <code>{`@[kanon_arm]{:lean}`}</code> theorem does.
    </li>
    <li>
      <strong>Lifting.</strong> The lifting lemma of a function with a subsort operand assumes the
      predicate of its argument, which <code>kanon_lift</code> leaves as a goal: if the body of a
      rule calls such a function, the goal <code>Nonzero v'</code> is left for the proof of that
      rule, from what that rule knows of <code>v'</code> (the example at the end of the proofs
      below). <code>kanon_lift_body</code>, which <code>kanon_rule</code> uses, leaves it with the
      hypothesis <code>kw</code> that the spec is well-typed, as the predicate usually only holds
      of well-typed terms; <code>kanon_rule</code> tries <code>kanon_rule_close</code> and the
      <code>kanon_close_lemma</code> lemmas on it, and leaves it otherwise. Functions have no sorts,
      so only rules assume or prove anything.
    </li>
    <li>
      <strong>Swaps.</strong> The arms that are derived from another by commutativity are proved as
      the others when there are assumptions, since their operands are other terms than those of the
      arm that they come from. The elements of a list of operands each satisfy the predicate
      (<code>∀ y ∈ vs, Nonzero y</code>).
    </li>
  </ul>
  {#each divisionProofs as [name, text] (name)}
    <p class="file"><code>examples/division/lean/{name}</code></p>
    <Code lang="lean" code={text} />
  {/each}
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
      <code>ev</code>): <code>KanonBool.Sem.ev_bool</code> needs well-typed booleans to evaluate to
      booleans.
    </li>
    <li>
      <strong>Values of their type.</strong> <code>ev_ty</code>, that well-typed terms evaluate to
      values of their type, is proved by recursion on terms (<code>Lang.lean</code>); the
      <code>ev_bool</code> of <code>lang</code> follows from it.
    </li>
    <li>
      <strong>Lists of operands.</strong> The typing law of a node with a list of operands
      (<code>WT_Distinct</code>) quantifies over its elements: give <code>kanon_law</code> the
      lemma that turns the language's typing of lists into it (<code>WTList_iff</code>, tagged
      <code>{`@[kanon_law]{:lean}`}</code>), and that of their evaluation
      (<code>evList_eq</code>).
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
      splits their <code>if</code>s (in a module proved once, rewrite with their laws,
      <code>bool_of_bool_eq</code>).
    </li>
    <li>
      <strong>Instances of the modules.</strong> The interface of a language
      (<code>modSyntax</code>) is not reducible: its laws unfold it by the simp set
      <code>kanon_law</code>. With <code>open Classical</code>, write the semantics of an
      application explicitly (<code>(S := sem)</code>), as the generated files do.
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
  <p>The proof of a larger language (Soteria's bit-vectors) ran into these:</p>
  <ul>
    <li>
      <strong>Names in tactics.</strong> The names that a <code>macro</code> quotes are resolved
      where it is defined: a lemma defined after the macro is unknown to it, and a
      <code>{`try simp [...]{:lean}`}</code> then silently does nothing. Give lemmas to the tactics by
      attributes (the simp sets above) rather than by name. With
      <code>set_option hygiene false</code> (to name, in a later tactic, a hypothesis that the
      macro introduces) every name is resolved where the macro is used: write them in full. The
      string of a <code>kanon_tactic</code> is parsed where the arms are proved, in the namespace
      of the model: qualify the names of other namespaces there too.
    </li>
    <li>
      <strong><code>rfl</code> patterns in macros.</strong> In a hygienic macro, the
      <code>rfl</code> of an <code>obtain</code> or <code>rcases</code> pattern is taken for a name
      and substitutes nothing: <code>{`have h : x = y := …; subst h{:lean}`}</code> instead.
    </li>
    <li>
      <strong>Simp side conditions.</strong> A conditional simp lemma whose hypothesis has a
      variable that its left-hand side does not determine is not used, silently: the hypothesis
      has a metavariable, which neither the default discharger nor a <code>disch</code> tactic
      proves. State the lemma so that its left-hand side, or its first hypotheses (which
      <code>assumption</code> discharges), determine every variable.
    </li>
    <li>
      <strong>Annotations of the congruence lemmas.</strong> When the sort of a node is not that of
      its spec (<code>ty v2</code> against a sort <code>t</code>), the congruence lemma has a side
      condition that <code>{`intro _; rfl{:lean}`}</code> does not prove: give
      <code>kanon_congr_side</code>, which must close it.
    </li>
    <li>
      <strong>Tactics of functions.</strong> A <code>kanon_auto</code> that tries several tactics
      in turn (<code>{`first | (t1; done) | (t2; done) | …{:lean}`}</code>) runs the failing ones
      on every arm, which can cost more than the proof. Give each function the tactic that proves
      its arms, which they try first:
      <code>{`attribute [kanon_tactic "kanon_rule_bounds"] Bool.and_.spec{:lean}`}</code>.
    </li>
    <li>
      <strong>The two halves of a refinement.</strong> Prove them by position
      (<code>{`refine Sem.Refines.intro ?_ ?_{:lean}`}</code>, then one tactic per goal, as
      <code>kanon_rule</code> does), not by trying the typing tactic on every goal
      (<code>{`all_goals first | (wt; done) | sem{:lean}`}</code>), which fails, slowly, on the value
      half.
    </li>
    <li>
      <strong><code>omega</code></strong> uses every hypothesis of the context and splits on its
      disjunctions, divisions and remainders: on an arm with many of them, a lemma for the step it
      is to make (or clearing the hypotheses it does not need) is much faster.
    </li>
  </ul>

  <Heading level={2} id="minimal">The minimal case</Heading>
  <p>
    <a href="{REPO}/examples/bool"><code>examples/bool</code></a> is the bool module alone, with
    booleans as values. Its rules are all the bool module's, which the library proves: it has no
    <code>kanon_auto</code>, hence no <code>Lib/</code>, no <code>Nodes.lean</code> and no
    <code>Proofs/</code>, and its hand-written files are its semantics, its primitives and its
    <code>lang</code>, whose one law to prove is <code>sure_neq_sound</code>. It is the template
    for a language that starts from the bool module.
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
