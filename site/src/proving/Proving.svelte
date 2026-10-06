<script lang="ts">
  // The guide to proving a language in Lean: the files to write, what Kanon's library gives, and
  // the proof loop, on the worked example examples/ints (a language and a module), whose
  // hand-written files are imported from the repository at build time.
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
      "../../../examples/division/lean/DivMod/*.lean",
      "../../../examples/two_langs/lean/WordMod/Prims.lean",
      "../../../lean/KanonBool/Prims.lean",
    ],
    { query: "?raw", import: "default", eager: true },
  ) as Record<string, string>;

  /** A file of the repository, by its path from its root. */
  function repo(path: string): string {
    const text = sources[`../../../${path}`];
    if (text === undefined) throw new Error(`proving: ${path} is not imported`);
    return text;
  }

  /** A file of examples/ints, by its path in that directory. */
  function file(path: string): string {
    return repo(`examples/ints/${path}`);
  }

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
    variables), proved in <code>examples/ints/lean</code>. Every module is proved once, for any
    language that has it, and a language only puts its modules together. Its hand-written files
    are quoted whole: they are templates.
    <a href="{REPO}/examples/bool"><code>examples/bool</code></a>, the bool module alone, is the
    minimal case, and <a href="{REPO}/examples/two_langs"><code>examples/two_langs</code></a> has
    five languages that share modules, with a diamond, invariants, data types, oracles and a
    binder.
  </p>
  {#each ["lang.knl", "int.knl", "int.kn"] as name (name)}
    <p class="file"><code>examples/ints/{name}</code></p>
    <Code code={file(name)} />
  {/each}

  <Heading level={2} id="files">The files</Heading>
  <p>
    Each module (a <code>.knl</code> file and its <code>.kn</code> file) has its Lean files in the
    namespace and directory of its root: <code>{`[@@@lean_root "R"]{:kanon}`}</code> in its
    <code>.knl</code>, else, for the language's own module (that of its first file), the root of
    the language (<code>Kanon</code> by default), and for another module the root of the language
    and its name (<code>IntsExample.Vec</code>). Here the int module is <code>IntMod</code> and the
    language <code>IntsExample</code>. <code>kanon lean-all DIR lang.knl</code> writes the
    generated files of every module under <code>DIR/R</code>, but those of the modules built into
    kanon (the bool module), which are in Kanon's library. A few files per module, each importing
    the files of the modules it uses: a change to a module rebuilds its files and those of the
    modules and languages that use it, never those of the modules it uses. Those of a module:
  </p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Types.lean</code></td>
        <td>Its data types, if it declares some (see <a href="#data">Data types</a>).</td>
      </tr>
      <tr>
        <td><code>Node.lean</code></td>
        <td>
          Its sorts, <code>Srt</code>, and its nodes, <code>{`Node (T : Type){:lean}`}</code>, over
          the terms <code>T</code> of any language, with the documentation comments of the
          declarations; <code>Node.map</code>, <code>Node.All</code> (every child satisfies a
          predicate) and <code>Node.Rel</code> (two nodes with the same arguments and related
          children). Sorts that take sorts are over the sorts of a language,
          <code>{`Srt (Ty : Type){:lean}`}</code>, and so are nodes that take sorts,
          <code>{`Node (Ty T : Type){:lean}`}</code> (see <a href="#sorts">Sorts of sorts</a>).
        </td>
      </tr>
      <tr>
        <td><code>Lang.lean</code></td>
        <td>
          The typing of its nodes, <code>Node.wt</code>, at the sorts of any language, and
          <code>{`class Lang (S : Kanon.Sem) [KanonBool.Lang S] … extends Values S.toDom{:lean}`}</code>:
          what it needs of a language <code>S</code>, given the instances of the modules it uses.
          Its values (<code>Values</code>, from <code>Sem.lean</code>), its nodes and sorts
          embedded in the terms and sorts of <code>S</code> (<code>node</code>,
          <code>srt</code>), which <code>S</code> types and evaluates as the module says
          (<code>WT_inj</code>, <code>ev_inj</code>), and which are not those of the other modules
          (<code>proj_Int_inj_Bool</code>, …). From them, <code>mk</code> (the term of a node),
          <code>proj</code> (the node of a term, if it is one), <code>sort</code> and
          <code>sortProj</code>, with their lemmas for the tactics. And
          <code>{`class Typed (S) … [Lang S] : Prop{:lean}`}</code>, if it has sorts: well-typed
          terms of its sorts evaluate to values of these sorts (<code>Srt.val</code>).
        </td>
      </tr>
      <tr>
        <td><code>Model.lean</code></td>
        <td>
          The model of its helpers and rules, over the terms of any language: its record
          <code>{`Ops S{:lean}`}</code> (which extends those of the modules it uses, or
          <code>Kanon.OpsBase</code>, the oracle <code>tag_le</code>) of its rule functions, oracles
          and extensible helpers, its helpers, the specs of its rule functions, each rule a
          function to <code>{`Option S.Term{:lean}`}</code>, and <code>Ops.Sound</code>, what the
          proofs assume of a model: that its rule functions refine their specs, and that its oracles
          and extensible helpers satisfy what <code>Prims.lean</code> says of them. The
          documentation comments of the helpers, the oracles and the rule functions are carried to
          it. A helper or a primitive marked <code>{`[@no_lean]{:kanon}`}</code> is not in it (nor in
          any other generated file).
        </td>
      </tr>
      <tr>
        <td><code>Statements.lean</code></td>
        <td>
          The lifting lemmas (<code>Lib.lift_f</code>: a spec is refined by the rule function on
          refined arguments), the commutativity of each <code>{`[@comm]{:kanon}`}</code> node
          (<code>Plus.comm.Stmt</code>), and the statement of each arm of each rule
          (<code>Int.plus.r_lits.main.Stmt</code>), for any language that has the module:
          <code>{`∀ {S : Kanon.Sem} [KanonBool.Lang S] [Lang S] [KanonBool.Typed S] [Typed S] (O : Ops S), O.Sound → …{:lean}`}</code>.
        </td>
      </tr>
      <tr>
        <td><code>Soundness.lean</code></td>
        <td>
          The proofs of the commutativities and of the arms (<code>{`kanon_proof% X{:lean}`}</code>,
          each with its own bound on heartbeats, see
          <a href="reference.html#floating"><code>{`[@@@lean_heartbeats]{:kanon}`}</code></a>), the
          arms that only swap commutative operands (from the commutativity), and each rule from its
          arms (<code>f.r_rule.sound</code>).
        </td>
      </tr>
    </tbody>
  </table>
  <p>And by hand, for each module:</p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Sem.lean</code></td>
        <td>
          The meaning of its nodes, for any language: <code>{`class Values (D : Kanon.Dom){:lean}`}</code>,
          the values it needs of a language (<code>{`vint : Embed Int D.Val{:lean}`}</code>), the
          evaluation of a node in an environment given the values of its children in every
          environment,
          <code>{`Node.eval (ρ : D.Env) (t : D.Ty) : Node (D.Env → Option D.Val) → Option D.Val{:lean}`}</code>
          (most nodes take those at <code>ρ</code>, <code>a ρ</code>; a binder those at others),
          that it is monotone (<code>Node.eval_mono</code>: poison children give poison or the same
          value), the values of its sorts (<code>Srt.val</code>), its invariants (see
          <a href="#invariants">Invariants</a>) and its primitives over plain data, which its typing
          may use.
        </td>
      </tr>
      <tr>
        <td><code>Prims.lean</code></td>
        <td>
          If it has some: its primitives over terms (the literals <code>v_true</code> of the bool
          module), the predicates of its subsorts (<code>Nonzero</code>), what its rules assume of
          its oracles (<code>Oracle.Compat</code>), and what its extensible helpers satisfy
          (<code>Bool.sure_neq.post</code>).
        </td>
      </tr>
      <tr>
        <td><code>Proofs.lean</code></td>
        <td>
          If it has some: the proofs that the tactics do not find, as
          <code>{`@[kanon_arm]{:lean}`}</code> theorems of the statements (see
          <a href="#loop">The proof loop</a>). <code>Soundness.lean</code> imports it when it
          exists.
        </td>
      </tr>
      <tr><td><code>Abstract.lean</code></td><td>Only if it declares abstract types: their Lean types (see <a href="#data">Data types</a>).</td></tr>
    </tbody>
  </table>
  <p>The language has its own files, under its root, the generated ones:</p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Syntax.lean</code></td>
        <td>
          Its sorts, <code>Ty</code>, a constructor per module with sorts
          (<code>{`.int (s : IntMod.Srt){:lean}`}</code>), and its terms, <code>Term</code>, a node
          of a module at a sort (<code>{`.int (n : IntMod.Node Term) (t : Ty){:lean}`}</code>).
        </td>
      </tr>
      <tr>
        <td><code>Semantics.lean</code></td>
        <td>
          The typing <code>Term.WT</code> and the evaluation <code>ev</code> of the terms, by those
          of the nodes of the modules, the semantics <code>sem</code> (a <code>Kanon.Sem</code>),
          <code>eval</code>, <code>Refines</code>, and the instance of <code>Lang</code> of each
          module, whose laws hold by <code>rfl</code>.
        </td>
      </tr>
      <tr>
        <td><code>Rules.lean</code></td>
        <td>
          The rule functions of the language: each the first of the rules of the modules that
          applies (<code>firstSome</code>), over the oracles (<code>Oracle</code>), its extensible
          helpers put together from the cases of its modules, the rule functions with fuel
          (<code>opsN</code>), and <code>opsN_sound</code>, the proof that the whole simplifier is
          sound, given <code>Oracle.Compat</code>, what the modules assume of their oracles.
        </td>
      </tr>
    </tbody>
  </table>
  <p>And by hand:</p>
  <table>
    <thead><tr><th>File</th><th>Contents</th></tr></thead>
    <tbody>
      <tr>
        <td><code>Val.lean</code></td>
        <td>
          Its values, <code>Val</code>, its environments, <code>Env</code>,
          <code>{`abbrev dom : Kanon.Dom{:lean}`}</code>, and the instance of the
          <code>Values</code> class of each module, with embeddings by its constructors, whose laws
          hold by cases.
        </td>
      </tr>
      <tr>
        <td><code>Typing.lean</code></td>
        <td>
          That well-typed terms evaluate to values of their sorts (<code>ev_ty</code>, by recursion
          on terms, with the generated <code>WT_int</code> and <code>ev_int</code>), and from it the
          instance of <code>Typed</code> of each module with sorts.
        </td>
      </tr>
    </tbody>
  </table>
  <p>
    The language's own module (here, the variables) is a module as any other: its
    <code>Sem.lean</code> evaluates the variables, by what it needs of the language (the values of
    the environment).
  </p>

  <Heading level={2} id="modules">Modules</Heading>
  <p>
    The module is proved for every language that has it, through its <code>Lang</code> class: its
    proofs are built once, and a change to a language (a node, a module, a rule of its own) does
    not rebuild them. A module uses the modules whose nodes, sorts, helpers or rule functions it
    mentions, and those it <code>use</code>s; modules cannot use each other (Kanon reports the
    cycle): merge them. A language's own module that a module uses (as the nodes of
    <code>lang.knl</code> that the rules of a <code>rules.kn</code> match) does not use the modules
    of the language that use it, and the rule functions of the language are those of the module
    that uses all the others.
  </p>
  <p>
    The arms that a module adds to the rules of another (<code>extend rule</code>) are proved with
    the module that adds them. A helper that other modules extend (<code>extend fn</code>) is
    marked <code>{`[@extensible]{:kanon}`}</code>, as the bool module's <code>sure_neq</code>; its
    body is then a <code>match</code> that ends with a case that always applies, it is a field of
    <code>Ops</code>, and each language puts its cases together, the first that applies, in
    <code>Rules.lean</code>. Its module states what it satisfies in <code>Prims.lean</code>
    (<code>Bool.sure_neq.post</code>), which each case of each module proves
    (<code>Bool.sure_neq.c1.Stmt</code>), as its default (<code>Bool.sure_neq.default.Stmt</code>),
    and which the rules of every module may use (<code>hO.bool_sure_neq</code>). A case that calls
    rule functions, oracles or extensible helpers (itself, on the children of a node) takes the
    record <code>O</code> of the model, and its statement assumes <code>O.Sound</code>: each
    language puts the cases together at each step of fuel, over the record of the step before,
    and the default alone at the first. The pack module of <code>examples/two_langs</code> tells
    two packs of one term apart by their terms.
  </p>
  <p>
    The oracles that the rules of a module call are fields of its <code>Ops</code>, and what it
    assumes of them is its <code>Oracle.Compat</code>, in <code>Prims.lean</code>, a field of its
    <code>Ops.Sound</code> (<code>bool_orc</code>), which the language assumes. The bool module's
    <code>sort_by_tag</code> permutes a list, and the word module of
    <code>examples/two_langs</code> folds a sum of literals with its oracle <code>wsum</code>:
  </p>
  <p class="file"><code>lean/KanonBool/Prims.lean</code></p>
  <Code lang="lean" code={repo("lean/KanonBool/Prims.lean")} />
  <p class="file"><code>examples/two_langs/lean/WordMod/Prims.lean</code></p>
  <Code lang="lean" code={repo("examples/two_langs/lean/WordMod/Prims.lean")} />

  <Heading level={3} id="data">Data types</Heading>
  <p>
    The records and variants that a module declares (<code>{`type flags = { wrap : bool; strict : bool }{:kanon}`}</code>)
    are defined once, for every language, in its generated <code>Types.lean</code>, under its
    namespace: <code>CfgMod.Flags</code>, or the name that <code>{`[@lean "Name"]{:kanon}`}</code>
    gives (<code>{`type mode [@lean "Rounding"] = Down | Up{:kanon}`}</code> is
    <code>CfgMod.Rounding</code>). Its abstract types are defined by hand, in its
    <code>Abstract.lean</code>, which may use those of <code>Types.lean</code> (but those that
    <code>{`[@lean]{:kanon}`}</code> names, which are existing Lean types,
    <code>{`type label [@lean "String"]{:kanon}`}</code>). A type that holds terms (or sorts) is
    over those of a language (<code>{`structure Two (T : Type){:lean}`}</code>), with the functions
    that map its terms and list them (<code>Two.map</code>, <code>Two.flat</code>); it cannot hold
    itself, nor use an abstract type of its module. The modules that use these types import them, so that their nodes
    take them as arguments (<code>{`WAdd (x1 : CfgMod.Flags) (n : Int) (a3 a4 : T){:lean}`}</code>),
    and their rules build and match them. In <code>examples/two_langs</code>, the cfg module
    declares data types only, which the nodes of the word module take.
  </p>

  <Heading level={3} id="diamonds">Diamonds</Heading>
  <p>
    The classes are unbundled: the <code>Lang</code> class of a module has its own fields only,
    and takes the instances of the modules it uses as parameters
    (<code>{`MixMod… [NumMod.Lang S] [EvenMod.Lang S] [NegMod.Lang S]{:lean}`}</code>). A module
    that two others use is then one instance, and the lemmas of the shared module rewrite the
    goals of both as they are. Its <code>Lang</code> class also states that its nodes and sorts are
    not those of the modules it uses, and of each pair of these that do not use each other (the
    even and neg modules, in <code>L3</code>): the first module that uses two modules tells them
    apart. Only <code>Ops</code> extends those of the modules used. In
    <a href="{REPO}/examples/two_langs"><code>examples/two_langs</code></a>, the neg and even
    modules use the num module, and the mix module uses both (the language <code>L3</code>).
  </p>

  <Heading level={3} id="invariants">Invariants</Heading>
  <p>
    The typing of a node (<code>Node.wt</code>) says what Kanon knows of it: the sorts of its
    typing, and the invariants of the node and of its sort. An invariant is a Lean predicate on the
    nodes of the module and their sort, over the same arguments as their typing (the embeddings
    of the sorts of the modules it uses, and the types of the children),
    <code>{`P {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sWord : Srt → Ty) (ty : T → Ty) : Node T → Ty → Prop{:lean}`}</code>,
    that its <code>Sem.lean</code> defines, declared on a sort or a node:
    <code>{`sort TEven [@lean_inv "even_inv"]{:kanon}`}</code> holds of the nodes whose typing gives
    that sort, and <code>{`node WFit of int (z) : TWord (fit z) [@lean_inv "word_wf"]{:kanon}`}</code>
    of that node. The nodes and sorts that name the same predicate share it. Tag it
    <code>{`@[kanon_wt]{:lean}`}</code> for the tactics to unfold it. The even module of
    <code>examples/two_langs</code> proves <code>Rem2 (Ev z) → 0</code>, which holds of even
    literals only. An invariant may state what the typing cannot: the pack module of
    <code>examples/two_langs</code> gives a pack the sort of its terms,
    <code>{`∃ e, t = sPack (.TPack e) ∧ ∀ x ∈ l, ty x = e{:lean}`}</code>.
  </p>

  <Heading level={3} id="sorts">Sorts of sorts and binders</Heading>
  <p>
    A sort may take sorts (<code>{`sort TPack of ty{:kanon}`}</code>), and a node may take sorts
    among its arguments (<code>{`node Some_ of (name * ty) list * t : TBool{:kanon}`}</code>): its
    <code>Srt</code> (or <code>Node</code>) is then over the sorts of a language,
    <code>{`Srt (Ty : Type){:lean}`}</code> (<code>{`Node (Ty T : Type){:lean}`}</code>), which the
    language gives (<code>{`.pack (s : PackMod.Srt Ty){:lean}`}</code>). The children of a node are
    given to its meaning in every environment, so that a binder evaluates its body in others: the
    quantifier <code>Some_</code> of the pack module of <code>examples/two_langs</code> is whether
    some environment that gives its names values makes its body true
    (<code>examples/two_langs/lean/PackMod/Sem.lean</code>), and the language
    <code>L5</code> proves the typing of its terms in every environment.
  </p>
  <p>
    The children of a node may be inside other types: an array, an option, a tuple, or a record
    or variant of the module (<code>{`node Opt of (int * t) option{:kanon}`}</code>). For each such
    type, <code>Node.lean</code> defines the functions that map its terms and list them
    (<code>Node.shape1.map</code>, <code>Node.shape1.flat</code>, with their lemmas), by which
    <code>Node.All</code> and <code>Node.Rel</code> see these children: two nodes are related when
    the values have the same shape and their lists of children are related. The packs of the pack
    module hold their terms in a list, an array, an option of a pair and a record.
  </p>

  <Heading level={3} id="laws">What a module needs a language to prove</Heading>
  <p>
    Some primitives read the terms of a language: the names that occur free in a term, which a
    rule that drops the unused names of a quantifier needs. A module marked
    <code>{`[@@@lean_laws]{:kanon}`}</code> declares, in its <code>Prims.lean</code>, the class
    <code>{`Laws (S : Kanon.Sem) [Lang S] …{:lean}`}</code> of what it needs of every language:
    these primitives, and the facts that its proofs use. Its statements assume it, and each
    language gives an instance in its <code>Typing.lean</code>, where it defines them on its terms
    and proves the facts by induction on them. The pack module's <code>used_names</code> keeps the
    names that occur free in the body of a quantifier; <code>L5</code> proves that the value of a
    term depends on its free names only, hence that the others do not change the quantifier.
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
      <code>Kanon.Dom</code>, the sorts, values and environments of a language, and
      <code>Kanon.Sem</code>, its semantics: its terms, with <code>ty</code>, <code>WT</code>
      (typing) and <code>ev</code> (evaluation, assuming typing). From them,
      <code>Sem.eval</code> (poison, <code>none</code>, for ill-typed terms) and
      <code>{`Sem.Refines spec r{:lean}`}</code>: <code>r</code> is well-typed, of the type of
      <code>spec</code>, when <code>spec</code> is, and has its value when <code>spec</code> has
      one, with its lemmas (<code>Sem.Refines.refl</code>, <code>trans</code>, <code>syn</code>,
      <code>ev</code>, <code>intro</code>, …) and the instance of <code>Refinement</code>;
    </li>
    <li>
      <code>{`Embed A B{:lean}`}</code> (<code>KanonCore.Embed</code>), an injection with its
      partial inverse, with which a module sees the values and sorts of a language, and
      <code>{`NodeEmbed N S{:lean}`}</code>, the nodes <code>N</code> of a module in the terms of
      <code>S</code>; <code>Forall₂</code>, the relation of the list children of two nodes;
    </li>
    <li>
      <code>whenSome</code> and <code>firstSome</code>, with which the model is written, and
      <code>Kanon.OpsBase</code>, the oracle <code>tag_le</code>; <code>arrayLength</code>,
      <code>arrayGet</code> and <code>arraySet</code> (<code>KanonCore.Array</code>), with which the
      model uses the arrays of the language (Lean's <code>Array</code>), and their lemmas;
    </li>
    <li>
      the attributes <code>kanon_spec</code> (the specs, which the tactics unfold),
      <code>{`kanon_tactic "tac"{:lean}`}</code> (on <code>f.spec</code>: the tactic that proves the
      arms of <code>f</code>; on <code>Ops</code>, that of the arms a module adds to the rules of
      another) and <code>kanon_arm</code> (on a theorem: the hand-written proof of a statement);
      <code>{`kanon_proof% X{:lean}`}</code> proves <code>X</code> by its <code>kanon_arm</code>
      theorem if there is one, else the <code>kanon_tactic</code> of its function, else
      <code>kanon_auto</code>.
    </li>
  </ul>

  <Heading level={3} id="proof">KanonCore.Proof</Heading>
  <p>The tactics of the proofs, imported on their own:</p>
  <ul>
    <li>
      <code>kanon_auto</code>, the default proof of an arm: <code>kanon_rule</code> for a
      refinement, else <code>kanon_post</code> (for what a rule or a case of a helper must
      satisfy). <code>kanon_rule_lift</code> takes the guard of an arm, unfolds its spec and the
      helpers of its body, splits their conditionals and matches, reads the nodes that the
      projections of the patterns return, lifts the calls of rule functions to their specs (with the
      lifting lemmas), and closes the refinements that are reflexivity or commutativity.
      <code>kanon_rule</code> then proves the typing half of the refinement and splits its value
      half on the values of the atoms (by the lemmas <code>ev_cases</code> of the modules, from
      their <code>Typed</code> class), closing what <code>simp_all</code>, <code>omega</code> and
      <code>grind</code> can.
    </li>
    <li>
      They are made of smaller ones, which are also available: <code>kanon_split</code>,
      <code>kanon_split_matches</code>, <code>kanon_proj</code>, <code>kanon_lift</code>,
      <code>kanon_lift_body</code>, <code>kanon_guards</code>, <code>kanon_lits</code>,
      <code>kanon_wt</code>, <code>kanon_sem_core</code>, <code>kanon_sem</code>,
      <code>kanon_close</code>, <code>kanon_refl</code>, <code>kanon_congr</code> (refinement by
      congruence, from <code>Node.eval_mono</code>) and <code>kanon_comm</code>. They match terms
      up to reducible definitions only, so that on different terms they fail without evaluating
      them.
    </li>
    <li>
      A module gives these tactics its lemmas by attributes: the simp sets
      <code>kanon_guards</code>, <code>kanon_body</code>, <code>kanon_lits</code>,
      <code>kanon_wt</code>, <code>kanon_ev</code>, <code>kanon_val</code> (the operations on
      values: <code>{`op2_eq_some{:lean}`}</code>) and <code>kanon_close_simp</code>, the values
      of the atoms (<code>kanon_atom_cases</code>) and closing lemmas
      (<code>kanon_close_lemma</code>); and it may extend the tactics
      <code>kanon_congr_side</code>, <code>kanon_rule_close</code> and
      <code>kanon_close_side</code>.
    </li>
  </ul>

  <Heading level={3} id="kanonbool">KanonBool</Heading>
  <p>
    The bool module (<code>modules/bool.knl</code> has
    <code>{`[@@@lean_root "KanonBool"]{:kanon}`}</code>), proved once, as any module: its
    generated files, its <code>Sem.lean</code> (the booleans <code>vbool</code>, and the
    evaluation of its nodes by <code>pand</code>, <code>por</code>, <code>pnot</code>,
    <code>peq</code>, <code>pite</code> and <code>pdistinct</code>), its <code>Prims.lean</code>
    and its <code>Proofs.lean</code>. A language does not generate its files: they are in the
    library.
  </p>

  <Heading level={2} id="steps">Step by step</Heading>

  <Heading level={3} id="project">The project</Heading>
  <p>
    A Lake package that requires Kanon's library, at the toolchain of <code>lean/</code>, with a
    library per root (<code>IntsExample.lean</code> imports <code>IntsExample.Rules</code>):
  </p>
  <Code lang="text" code={file("lean/lakefile.toml")} />
  <p>
    The generated files are written by <code>kanon lean-all . ../lang.knl</code>, run in
    <code>examples/ints/lean</code> (in Kanon's repository, <code>dune test</code> runs
    <code>kanon lean-all --check</code>, which checks that they are up to date). The files of a
    module import each other in this order, the hand-written ones in bold:
  </p>
  <p class="chain">
    <code>Types</code> → <strong><code>Abstract</code></strong> → <code>Node</code> →
    <strong><code>Sem</code></strong> → <code>Lang</code> → <strong><code>Prims</code></strong> →
    <code>Model</code> → <code>Statements</code> → <strong><code>Proofs</code></strong> →
    <code>Soundness</code>
  </p>
  <p>And those of the language, after those of its modules:</p>
  <p class="chain">
    <code>Syntax</code> → <strong><code>Val</code></strong> → <code>Semantics</code> →
    <strong><code>Typing</code></strong> → <code>Rules</code>
  </p>
  <p>
    <code>kanon lean-all</code> imports a hand-written file when it exists: run it after adding
    one. <code>check_axioms.lean</code> checks that the soundness theorem is proved, without
    <code>sorry</code>:
  </p>
  <Code lang="lean" code={file("lean/check_axioms.lean")} />

  <Heading level={3} id="sem">IntMod/Sem.lean</Heading>
  <p>
    What the int module needs of a language, its integers, and the evaluation of its nodes, by an
    operation on two integers that is poison when an operand is, or is not an integer. Its lemma
    <code>op2_eq_some</code>, tagged <code>kanon_val</code>, is how the tactics read a value.
  </p>
  <Code lang="lean" code={file("lean/IntMod/Sem.lean")} />
  <p>
    Here the tactics prove every arm of the module's rules (<code>Int.plus</code>,
    <code>Int.int_lt</code>, the rule <code>ints</code> that it adds to <code>Bool.eq</code>, the
    case it adds to <code>sure_neq</code>) and the commutativity of <code>+</code>: it has no
    <code>Proofs.lean</code>.
  </p>

  <Heading level={3} id="lang-sem">IntsExample/Sem.lean</Heading>
  <p>
    The language's own module, the variables: a variable is the value of the environment, if it is
    of its sort, and poison otherwise.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Sem.lean")} />

  <Heading level={3} id="val">Val.lean</Heading>
  <p>
    The values of the language and the instances of the <code>Values</code> classes: the bool
    module's booleans and the int module's integers are constructors of <code>Val</code>.
    <code>dom</code> is an <code>abbrev</code>, so that the instances are found at
    <code>sem.toDom</code>.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Val.lean")} />

  <Heading level={3} id="typing">Typing.lean</Heading>
  <p>
    That well-typed terms evaluate to values of their sort, by recursion on terms, and the
    <code>Typed</code> instances of the modules with sorts, from it.
  </p>
  <Code lang="lean" code={file("lean/IntsExample/Typing.lean")} />

  <Heading level={2} id="loop">The proof loop</Heading>
  <ol>
    <li>
      <p>
        <code>lake build</code>. <code>Soundness.lean</code> proves each arm <code>X</code> by
        <code>{`theorem X.ok : X.Stmt := no_implicit_lambda% (kanon_proof% X){:lean}`}</code>; an
        arm that its tactic does not prove is an error there, at its theorem (or exceeds its
        heartbeats, and fails then).
      </p>
    </li>
    <li>
      <p>
        Read its statement in <code>Statements.lean</code>: for any language that has the module,
        its result refines its spec, over the variables of its pattern, with its guard as a
        hypothesis.
      </p>
      <Code
        lang="lean"
        code={`def Int.plus.r_lits.main.Stmt : Prop :=
  ∀ {S : Kanon.Sem} [KanonBool.Lang S] [IntMod.Lang S] [KanonBool.Typed S] [IntMod.Typed S] (O : Ops S), O.Sound →
  ∀ (i1 : Int) (t__2 : S.Ty) (i2 : Int) (t__4 : S.Ty),
  S.Refines (IntMod.Int.plus.spec (IntMod.mk (.Int i1) t__2) (IntMod.mk (.Int i2) t__4))
  ((IntMod.mk (.Int (IntMod.Int.add i1 i2)) (IntMod.sort .TInt)))`}
      />
    </li>
    <li>
      <p>
        Give the tactics the lemma they miss (by its attribute, in <code>Sem.lean</code> or
        <code>Prims.lean</code>), or a function a tactic of its own, which its arms try before
        <code>kanon_auto</code>:
      </p>
      <Code lang="lean" code={`attribute [kanon_tactic "kanon_int"] Int.plus.spec`} />
      <p>
        or prove the statement by hand, in the module's <code>Proofs.lean</code>: a theorem
        <code>X.proof</code> of <code>X.Stmt</code>, tagged <code>{`@[kanon_arm]{:lean}`}</code>
        (then run <code>kanon lean-all</code> if the file is new, so that
        <code>Soundness.lean</code> imports it). Editing it rebuilds the module's
        <code>Soundness.lean</code> and what imports it only.
      </p>
    </li>
    <li>
      <p>
        Each <code>{`[@comm]{:kanon}`}</code> node has one statement, <code>Plus.comm.Stmt</code>
        (<code>{`a + b{:kanon}`}</code> is refined by <code>{`b + a{:kanon}`}</code>), proved by
        <code>kanon_auto</code> or by hand. From it, and <code>kanon_congr</code>, Kanon proves the
        arms that only swap commutative operands (<code>swap</code>), if their guard and body do not
        depend on the swap: the proofs to write are at most one per case of a rule, and one per
        commutative node.
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
    <a href="{REPO}/examples/division"><code>examples/division</code></a> is a language of integers,
    with no booleans, that has a division whose divisor is a <code>TNonzero</code>, and a node
    <code>Sq1</code> that returns one.
  </p>
  <ul>
    <li>
      <strong>The predicate</strong>, <code>{`Nonzero : S.Term → Prop{:lean}`}</code>, which you
      write in the module's <code>Prims.lean</code>, for any language:
      <code>{`∀ ρ z, S.eval ρ e = some (Values.vint.inj z) → z ≠ 0{:lean}`}</code>. An invariant
      (<a href="#invariants">Invariants</a>) is a predicate of the same kind, over nodes, that
      well-typedness gives rather than the rules assume.
    </li>
    <li>
      <strong>What it assumes.</strong> A rule function with an operand of the subsort is stated
      for the terms that satisfy it: <code>Nonzero v2 →</code> is a hypothesis of its rules, its
      arms and its lifting lemma, and of <code>Ops.Sound</code>. The proofs that Kanon generates
      thread it, and <code>kanon_auto</code> proves an arm that does not need it. An arm that does,
      like <code>a / a = 1</code> (the quotient by zero is zero), is proved by hand, using the
      hypothesis.
    </li>
    <li>
      <strong>What it proves.</strong> A rule function whose node returns a subsort has to prove
      that what it returns, a rule or its spec, satisfies the predicate:
      <code>sq1.r_default.main.post.Stmt</code> and <code>sq1.spec_post.Stmt</code>, which are
      fields of <code>Ops.Sound</code> (<code>int_sq1_post</code>), so that the rules that call
      it may use them.
    </li>
    <li>
      <strong>Lifting.</strong> The lifting lemma of a function with a subsort operand assumes the
      predicate of its argument, which <code>kanon_lift</code> leaves as a goal, for the proof of
      the rule.
    </li>
  </ul>
  {#each ["Prims.lean", "Proofs.lean"] as name (name)}
    <p class="file"><code>examples/division/lean/DivMod/{name}</code></p>
    <Code lang="lean" code={repo(`examples/division/lean/DivMod/${name}`)} />
  {/each}

  <Heading level={2} id="pitfalls">Pitfalls</Heading>
  <ul>
    <li>
      <strong>Typed variables.</strong> With values of several types, a variable must evaluate to a
      value of its sort (<code>{`if Values.sortOf v = t then some v else none{:lean}`}</code>):
      the <code>Typed</code> class of the bool module needs well-typed booleans to evaluate to
      booleans.
    </li>
    <li>
      <strong>Sorts with several values.</strong> When the values of a sort are not those of one
      constructor (several sorts share the integers, as <code>TWord n</code>), state
      <code>ev_ty</code> with a relation (<code>{`Val.Of : Val → Ty → Prop{:lean}`}</code>), as the
      languages of <code>examples/two_langs</code> do.
    </li>
    <li>
      <strong>Values of the module.</strong> State the operations of <code>Sem.lean</code> with a
      lemma <code>op_eq_some</code> (tagged <code>kanon_val</code>) that says when they are
      <code>some</code>, and prove <code>Node.eval_mono</code> from their monotony.
    </li>
    <li>
      <strong>Names in tactics.</strong> The names that a <code>macro</code> quotes are resolved
      where it is defined: give lemmas to the tactics by attributes (the simp sets above) rather
      than by name. The string of a <code>kanon_tactic</code> is parsed where the arms are proved,
      in the namespace of the module: qualify the names of other namespaces.
    </li>
    <li>
      <strong>Simp side conditions.</strong> A conditional simp lemma whose hypothesis has a
      variable that its left-hand side does not determine is not used, silently. State the lemma
      so that its left-hand side, or its first hypotheses, determine every variable.
    </li>
    <li>
      <strong>Tactics of functions.</strong> A tactic that tries several others in turn runs the
      failing ones on every arm, which can cost more than the proof. Give each function the tactic
      that proves its arms: <code>{`attribute [kanon_tactic "…"] Bool.and_.spec{:lean}`}</code>.
    </li>
    <li>
      <strong><code>omega</code></strong> uses every hypothesis of the context and splits on its
      disjunctions, divisions and remainders: on an arm with many of them, a lemma for the step it
      is to make is much faster.
    </li>
  </ul>

  <Heading level={2} id="minimal">The minimal case</Heading>
  <p>
    <a href="{REPO}/examples/bool"><code>examples/bool</code></a> is the bool module and variables,
    with booleans as values. Its rules are all the bool module's, which the library proves: its
    hand-written files are the <code>Sem.lean</code> of its variables, its <code>Val.lean</code>
    and its <code>Typing.lean</code>. It is the template for a language that starts from the bool
    module.
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
