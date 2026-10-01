<script lang="ts">
  // The tutorial: what Kanon is, then a tiny language built step by step, with the code that
  // Kanon generates from each step.
  import {
    Callout,
    ContextMenuHost,
    DialogHost,
    Heading,
    Kbd,
    TableOfContents,
    ToastHost,
    headingsIn,
    type TocItem,
  } from "purr";
  import { Flask, Info } from "purr/icons";
  import Code from "../components/Code.svelte";
  import Header from "../components/Header.svelte";
  import Example from "./Example.svelte";

  let article = $state<HTMLElement | null>(null);
  let toc = $state<TocItem[]>([]);
  let current = $state<string | undefined>();

  $effect(() => {
    if (!article) return;
    toc = headingsIn(article, { selector: "h2" });
    const seen = new IntersectionObserver(
      (entries) => {
        for (const e of entries) if (e.isIntersecting) current = e.target.id;
      },
      { rootMargin: "-10% 0px -75% 0px" },
    );
    article.querySelectorAll("h2[id]").forEach((h) => seen.observe(h));
    return () => seen.disconnect();
  });
</script>

<ContextMenuHost />
<DialogHost />
<ToastHost />

<Header page="tutorial" />

<div class="layout">
  <aside class="toc">
    <TableOfContents items={toc} title="Contents" {current} />
  </aside>

  <article class="md" bind:this={article}>
    <h1>Kanon</h1>
    <p class="lede">
      Kanon is a rule language for the <em>simplifying smart constructors</em> of a value language:
      the functions that build its terms (<code>b_and a b</code>, <code>bv_add c a b</code>, …) and
      simplify them on the fly. You declare the language and write the rules; Kanon generates their
      OCaml implementation and a Lean model of them, with one soundness statement per rule and the
      proof that the whole simplifier is sound from the proofs of these statements.
    </p>
    <p>From the rules, the <code>kanon</code> tool generates:</p>
    <ul>
      <li>their OCaml implementation, meant to be included in the module that defines the terms;</li>
      <li>an OCaml check that the OCaml types of the language agree with its declaration;</li>
      <li>OCaml differential tests of the rule functions;</li>
      <li>
        a Lean model of the rules, with one soundness statement per rule, and the proof that the
        whole simplifier is sound from the proofs of these statements.
      </li>
    </ul>
    <p>
      The value language (its types, nodes, literals, operators and their laws) is declared in
      <code>.knl</code> files: Kanon does not hard-code any. The targets are fixed: OCaml, where
      terms are hash-consed (<code>Hc</code>) records <code>{"{ kind; ty }"}</code>, and Lean, where
      they are <code>Term.mk kind ty</code>. Kanon is a small, pure, first-order language with its own
      typing; its syntax is that of OCaml, apart from its declarations and the names of rules.
    </p>
    <Callout tone="info" title="Live examples">
      {#snippet icon()}<Flask />{/snippet}
      This tutorial builds a tiny language of booleans and integers, step by step. The code next to
      each step is generated in your browser, by Kanon compiled to JavaScript, and every step opens
      in the <a href="sandbox.html">sandbox</a>, an editor with Kanon's language server.
    </Callout>

    <Heading level={2} id="declare">Declaring a language</Heading>
    <p>
      A language is declared in <code>.knl</code> files, by <code>use</code>, <code>type</code>,
      <code>node</code>, <code>infix</code>, <code>prefix</code> and <code>constant</code> items. Its
      types are those of its OCaml AST. <code>kind</code> and <code>ty</code>, the kinds and the types
      (sorts) of terms, must be declared; <code>t</code> (terms), <code>int</code> (arbitrary
      precision, <code>Z.t</code> in OCaml), <code>bool</code>, <code>unit</code>, tuples,
      <code>option</code> and <code>list</code> are built in.
    </p>
    <Code
      code={`type var [@ocaml "string"] [@lean "String"] [@noeq]

type kind [@ocaml "t_kind"] [@noeq] =
  | Var of var
  | Unop of unop * t [@operators]
  | Binop of binop * t * t [@operators]`}
    />
    <ul>
      <li>
        <code>[@ocaml "..."]</code> and <code>[@lean "..."]</code> give the OCaml and Lean types, if
        they are not the Kanon name (CamelCased in Lean).
      </li>
      <li><code>[@noeq]</code>: <code>=</code> and <code>&lt;&gt;</code> are not allowed at this type.</li>
      <li>
        <code>[@operators]</code> on a kind constructor: the constructors of the type of its first
        argument are node constructors too, <code>Plus (l, r)</code> standing for
        <code>Binop (Plus, l, r)</code>.
      </li>
    </ul>
    <p>
      A <code>node</code> declares a constructor, with its arguments and its <em>typing</em>: the
      sorts of its operands, then of its result. Kanon places each node in the types of the language:
      an operator on two terms in <code>binop</code> (the operators of the <code>[@operators]</code>
      constructor with two terms), a sort in <code>ty</code>, and the other nodes in
      <code>kind</code>. A type that only has nodes is declared without constructors.
    </p>
    <Code
      code={`node Bool of bool [@literal] [@to_term of_bool]
node Int of int [@literal int]
node Not : TBool -> TBool
node Eq : a -> b -> TBool when a = b
node TBool`}
    />
    <ul>
      <li>
        <code>Eq</code> has operands of any sorts <code>a</code> and <code>b</code> (free variables),
        under the condition <code>a = b</code>, and a boolean result. Kanon generates the typing of
        each operator in Lean.
      </li>
      <li>
        <code>[@literal]</code> marks the node of the boolean literals, which <code>true</code> and
        <code>false</code> match in patterns, and <code>[@literal int]</code> that of the integer
        literals, which <code>0</code>, <code>1</code>, … and <code>#x</code> match.
        <code>[@to_term f]</code> gives the function that makes the literal of a boolean.
      </li>
    </ul>
    <p>
      This is enough for the backends that only need the declarations: the OCaml check of the types,
      and the Lean types and syntax.
    </p>
    <Example id="declare" ocaml="ocaml-check" lean="lean-types" />

    <Heading level={2} id="laws">Operators and laws</Heading>
    <p>
      Attributes on a node declare its algebraic laws, from which Kanon derives the first rules of
      its <em>rule function</em> (the function whose spec is the node over its parameters), before
      the rules written by hand. The derived rules are ordinary rules: they are generated and proved
      like the others.
    </p>
    <Code
      code={`node Not : TBool -> TBool [@invol]
node And : TBool -> TBool -> TBool [@comm] [@idem] [@unit true] [@zero false]
node Plus : TInt -> TInt -> TInt [@comm]`}
    />
    <table>
      <thead>
        <tr><th>Law</th><th>Derived rule (in <code>bv_add</code>, <code>bv_neg</code>, …)</th></tr>
      </thead>
      <tbody>
        <tr>
          <td><code>[@comm]</code></td>
          <td>the operands commute: the rules match them in either order</td>
        </tr>
        <tr>
          <td><code>[@fold f]</code></td>
          <td><code>lits: #l + #r -> f l r</code>, <code>lit: #bv -> f bv</code></td>
        </tr>
        <tr><td><code>[@unit c]</code></td><td><code>zero: x + 0 -> x</code></td></tr>
        <tr>
          <td><code>[@zero c]</code></td>
          <td>
            <code>zero: _ * 0 -> bv_zero (size v1)</code>,
            <code>false_: _ &amp;&amp; false -> v_false</code>
          </td>
        </tr>
        <tr><td><code>[@idem]</code></td><td><code>same: v &amp;&amp; v -> v</code></td></tr>
        <tr>
          <td><code>[@invol]</code></td>
          <td><code>neg: -x -> x</code>, named after the operator (unary operators)</td>
        </tr>
        <tr>
          <td><code>[@distrib_ite]</code></td>
          <td>
            <code>ite: Ite (b, l, r) -> b_ite b (bv_neg checked l) (bv_neg checked r)</code> (unary
            operators)
          </td>
        </tr>
      </tbody>
    </table>
    <p>
      <code>[@fold f]</code> folds literals with the function <code>f</code>, and
      <code>[@unit c]</code> and <code>[@zero c]</code> take the literal <code>0</code>,
      <code>1</code>, <code>true</code> or <code>false</code>, whose term the language declares with
      <code>constant</code>.
    </p>
    <Callout tone="neutral">
      {#snippet icon()}<Info />{/snippet}
      On numbers, these laws need literals whose values have an abstract type (<code
        >[@literal t]</code
      >, such as bit-vectors, <a href="#real">below</a>): the tiny language, with
      <code>[@literal int]</code>, writes the rules of <code>Plus</code> by hand.
    </Callout>
    <p>
      Operators give a syntax to nodes. <code>infix "op" = Node, f</code> declares what
      <code>a op b</code> builds and matches: in expressions, it calls the smart constructor
      <code>f</code>; in patterns, it matches the node. The operators are <code>+</code>,
      <code>-</code>, <code>*</code>, <code>land</code>, <code>lor</code>, <code>lxor</code>,
      <code>lsl</code>, <code>lsr</code>, <code>asr</code>, <code>++</code>,
      <code>&amp;&amp;</code>, <code>||</code> and <code>==</code>, the prefix <code>-</code>,
      <code>~</code> and <code>not</code>, and any word, which is then an infix operator in the rest
      of the files.
    </p>
    <Code
      code={`infix "&&" = And, and_
infix "+" = Plus, plus
prefix "not" = Not, not_

constant "true" (v) = v_true
constant "false" (v) = v_false`}
    />
    <p>
      The rules are in <code>.kn</code> files, which the language uses (<code>use "rules"</code>
      reads <code>rules.knl</code> and <code>rules.kn</code>, either of which may be missing). A rule
      function without a body, <code>rule f : spec</code>, only has the rules derived from the laws
      of its spec, and <code>default</code>, which builds the spec. Primitives (<code>prim</code>)
      are implemented by hand, in OCaml and in Lean.
    </p>
    <Code
      code={`prim v_true : t
prim v_false : t

rule not_ : Not v
rule and_ : And (v1, v2)`}
    />
    <p>
      The generated <code>and_</code> tries the rules of the laws in order, each in both orders of the
      operands, and the Lean statements say that each of them refines its spec.
    </p>
    <Example id="laws" ocaml="ocaml" lean="lean-statements" />

    <Heading level={2} id="rules">Rules</Heading>
    <p>
      <code>rule f : e = | r: p -> body | ...</code> declares a rule function, which returns a term
      that must <em>refine</em> the raw term <code>e</code>, its spec. When the spec is a node over
      variables, they are the parameters of the function. Its cases match the operands of the spec
      (as a tuple when there are several), and each is a rule, named by the label before its pattern;
      rules are tried in order. Unless its last case matches anything, a rule function ends with the
      rule <code>default</code>, which builds its spec.
    </p>
    <Code
      code={`rule plus : Plus (v1, v2) =
  | lits: #x + #y -> int (x + y)
  | zero: x + 0 -> x
  | assoc: (x + #a) + #b -> x + int (a + b)`}
    />
    <ul>
      <li>
        Patterns match the kind of a term directly. <code>0</code>, <code>1</code>, … match integer
        literals, <code>#_</code> any of them, and <code>#x</code> binds one; <code>true</code> and
        <code>false</code> match boolean literals.
      </li>
      <li>
        In expressions, <code>x + int (a + b)</code> calls the smart constructor <code>plus</code>
        again, and <code>a + b</code> on integers is the sum of integers. Nodes build raw terms,
        without simplification: <code>Plus (l, r)</code>.
      </li>
      <li>
        The spec <code>Plus (v1, v2)</code> is commutative: the cases match its operands in either
        order, unless the pattern is symmetric. The cases must then name the operands rather than use
        <code>v1</code> and <code>v2</code>. The operands of commutative operators in patterns match
        in either order too: <code>x + #a</code> also matches <code>#a + x</code>.
      </li>
      <li>
        <code>p [@comm]</code> also matches the components of the pair <code>p</code> swapped, for
        the operands of a node that does not commute.
      </li>
    </ul>
    <Code
      code={`rule and_ : And (v1, v2) =
  | not_: x && not x -> v_false

rule eq : Eq (v1, v2) =
  | same: x == x -> v_true
  | lits: #x == #y -> of_bool (x = y)
  | neg: #x == y when x < 0 && is_nat y -> v_false`}
    />
    <ul>
      <li>A repeated variable matches equal terms: <code>x &amp;&amp; not x</code>.</li>
      <li>
        <code>when</code> guards, or-patterns, <code>as</code>, <code>Some</code>/<code>None</code>,
        lists and partial records are supported.
      </li>
      <li>
        A case that an earlier case without a guard already matches can never be taken: Kanon leaves
        it out.
      </li>
    </ul>
    <p>
      Helpers are functions, <code>fn f params : ty = body</code>; all functions can call each other.
      <code>prim f : a -> b</code> declares a primitive, implemented by hand in OCaml (in a module
      <code>P</code>) and in Lean, and <code>oracle f : a -> b</code> one that the Lean model takes
      as a parameter, so that the proofs may not rely on its behaviour (e.g. a hash-consing order).
    </p>
    <Code
      code={`fn of_bool (b : bool) : t = if b then v_true else v_false

(* Whether a term is surely a natural number. *)
fn is_nat (v : t) : bool =
  match v with
  | Int n -> n >= 0
  | l + r -> is_nat l && is_nat r
  | _ -> false`}
    />
    <p>
      In the Lean model, every rule is a function to <code>Option Term</code>, and a rule function
      the first of its rules that applies:
    </p>
    <Example id="rules" ocaml="ocaml" lean="lean-model" />

    <Heading level={2} id="modules">Modules</Heading>
    <p>
      A language is made of the modules it uses, each with its declarations (<code>int.knl</code>)
      and its rules, primitives and helpers (<code>int.kn</code>). <code>use "path"</code> uses a
      module relative to the file, and <code>use +bool</code> the module of booleans built into
      <code>kanon</code>: boolean literals, <code>Not</code>, <code>And</code>, <code>Or</code>,
      equality (<code>Eq</code>), conditionals (<code>Ite</code>) and <code>Distinct</code>, with
      their rules. The language declares its types, as its OCaml AST has them, and Kanon places the
      nodes of the modules in them.
    </p>
    <Code
      code={`use +bool
use "int"

type kind [@ocaml "t_kind"] [@noeq] =
  | Var of var
  | Unop of unop * t [@operators]
  | Binop of binop * t * t [@operators]
  | Triop of triop * t * t * t [@operators]
  | Nop of nop * t list [@operators]

type nop = Distinct`}
    />
    <p>
      <code>Distinct</code> has a list of operands: the language places it itself, by naming it alone
      in a type. A module adds rules to the rule function of a module below it with
      <code>extend rule f</code>: last, but before its final catch-all case, or before its rule
      <code>r</code> with <code>extend rule f before r</code>. <code>extend fn</code> adds cases to a
      helper, here the literals of <code>int</code> to the bool module's <code>sure_neq</code>.
    </p>
    <Code
      code={`extend rule sem_eq before same =
  | ints: #x == #y -> of_bool (x = y)

extend fn sure_neq =
  | Int x, Int y -> not (x = y)`}
    />
    <p>
      A word declared as an operator, like <code>lt</code> below, is an infix operator in the rest of
      the files, and no longer a name.
    </p>
    <Example id="modules" ocaml="ocaml" lean="lean-soundness" />

    <Heading level={2} id="real">A real language</Heading>
    <p>
      Soteria's symbolic values are written in Kanon. An excerpt of its bit-vectors: literals of an
      abstract type, read and built by primitives, sorts with a width, laws, and rules that combine
      them.
    </p>
    <Code
      code={`type bv [@lean "BvVal"] [@equal "bv_equal"]

node BitVec of int [@literal bv] [@to_term lit] [@of_term bv_of_lit]
    [@raw to_z lit_to_z] [@raw width lit_width]
node BvNot : TBitVector n -> TBitVector n [@fold lit_not] [@distrib_ite]
node Add of checked : TBitVector n -> TBitVector n -> TBitVector n [@comm]
    [@fold lit_add]
node Mul of checked : TBitVector n -> TBitVector n -> TBitVector n [@comm]
    [@fold lit_mul] [@unit 1] [@zero 0]

infix "+" = Add, bv_add unchecked, lit_add

rule bv_add : Add (checked, v1, v2) =
  | neg: x + -y -> x - y
  | zero: x + 0 -> x
  | not_one: ~x + 1 -> -x
  | add_const: Add (c, #k1, r) + #k2 ->
      let checked = fold_checked (checked_meet checked c) k1 k2 true in
      bv_add checked (k1 + k2) r
  | sub_cancel: r + (l - r) -> l`}
    />
    <p>
      Here <code>infix "+" = Add, bv_add unchecked, lit_add</code> builds with
      <code>bv_add unchecked</code> in expressions, matches <code>Add (_, a, b)</code> whatever its
      parameter, and is the primitive <code>lit_add</code> on the values of literals.
    </p>

    <Heading level={2} id="generated">What Kanon generates</Heading>
    <p>
      <code>kanon BACKEND FILE...</code> reads the language declared by the files, usually its one
      <code>.knl</code> file, and writes on standard output:
    </p>
    <dl>
      <dt><code>ocaml</code></dt>
      <dd>
        the rule functions and helpers, in terms of a module <code>P</code> of primitives, which must
        be in scope where the code is included (the ppx <code>kanon.ppx_include_file</code> includes
        it: <code>[%%include_file "rules.gen.ml"]</code>);
      </dd>
      <dt><code>ocaml-check</code></dt>
      <dd>the check of the OCaml types of the language;</dd>
      <dt><code>ocaml-tests</code></dt>
      <dd>
        for every rule function, its spec, a call to it and the name of the rule that fires, from
        random arguments, to be compared by evaluation;
      </dd>
      <dt>
        <code>lean-types</code>, <code>lean-syntax</code>, <code>lean-signatures</code>,
        <code>lean-typing</code>, <code>lean-model</code>, <code>lean-statements</code>,
        <code>lean-lifts</code>, <code>lean-soundness</code>
      </dt>
      <dd>the generated Lean files (below); <code>lean-all</code> writes each of them.</dd>
    </dl>
    <p>
      The generated OCaml asserts the sorts of the operands on entry to each rule function (compiled
      out with <code>-noassert</code>), and puts the operands of commutative operators in the
      hash-consing order. The <a href="sandbox.html">sandbox</a> shows every backend on your own files.
    </p>

    <Heading level={2} id="proofs">Proofs</Heading>
    <p>
      The Lean files are generated in the namespace of <code>[@@@lean_root "R"]</code>
      (<code>Kanon</code> by default):
    </p>
    <ul>
      <li>
        <code>Types.lean</code> and <code>Syntax.lean</code> define the types of the language, and
        <code>Typing.lean</code> the typing of the operators;
      </li>
      <li>
        <code>Signatures.lean</code> checks that the hand-written <code>R.Prims</code> defines the
        primitives, at their types;
      </li>
      <li><code>Model.lean</code> is a model of the rule functions, over the primitives;</li>
      <li>
        <code>Statements.lean</code> states that every alternative of every rule is sound: its result
        refines its spec;
      </li>
      <li><code>Lifts.lean</code> states that the specs are monotone in their term arguments;</li>
      <li>
        <code>Soundness.lean</code> proves each rule from its alternatives, and every function from
        its rules, up to <code>R.opsN_sound</code>: the whole simplifier is sound.
      </li>
    </ul>
    <p>
      Written by hand, for each language: the abstract types (<code>R.Abstract</code>), the
      primitives (<code>R.Prims</code>), the semantics of terms and the refinement
      <code>Refines</code> (<code>R.Semantics</code>), and the tactics of the proofs. The language
      gives the tactic <code>kanon_auto</code>, the default proof of an alternative (an
      <em>arm</em>), with <code>kanon_comm</code> and <code>kanon_congr</code>; an arm that
      <code>kanon_auto</code> does not prove gets a theorem tagged <code>@[kanon_arm]</code>. Kanon's
      Lean library (<code>lean/</code>, the package <code>kanon</code>) gives what does not depend on
      the language.
    </p>
    <p>
      <code>examples/bool/</code> is a complete example: the bool module alone, with its Lean proof
      in <code>lean/</code>. Its semantics has booleans as values and <code>none</code> as poison;
      its <code>kanon_auto</code> proves an arm by case analysis on the values of the subterms it
      does not inspect, and the arms of <code>b_distinct</code>, on lists of terms, are proved by
      hand. To check it:
    </p>
    <Code
      lang="text"
      code={`cd examples/bool/lean
lake build
lake env lean check_axioms.lean  # must not mention sorryAx`}
    />
    <p><a class="btn" href="sandbox.html#example=bool">Open the bool example in the sandbox</a></p>

    <Heading level={2} id="editors">Editors</Heading>
    <ul>
      <li>
        <code>kanon lsp</code> is a language server: as files are edited, it checks the whole language
        they belong to and reports its errors, and it gives definitions, hovers, completion and
        symbols. It checks a <code>.kn</code> file with each <em>root</em> of the workspace that uses
        it, the <code>.knl</code> files that no other file uses (e.g. <code>lang.knl</code>).
      </li>
      <li>
        <code>tree-sitter-kanon/</code> is the tree-sitter grammar of <code>.kn</code> and
        <code>.knl</code> files; it highlights the code of this page.
      </li>
      <li>
        <code>editors/zed/</code> is the Zed extension: the language server, highlighting, the outline
        of a file down to its rules, brackets, indentation, text objects and snippets. Install it with
        <em>zed: install dev extension</em>, from that directory.
      </li>
    </ul>
    <p>
      The <a href="sandbox.html">sandbox</a> runs the same language server in your browser:
      <Kbd hint="F12" /> goes to a definition, and hovering a name shows its declaration.
    </p>
  </article>
</div>

<style>
  .layout {
    display: grid;
    grid-template-columns: 14rem minmax(0, 1fr);
    gap: calc(var(--sp-5) * 2);
    max-width: 1240px;
    margin: 0 auto;
    padding: 0 calc(var(--sp-5) * 2) calc(var(--sp-5) * 4);
  }
  .toc {
    position: sticky;
    top: calc(var(--btn) + var(--sp-5) * 3);
    align-self: start;
    margin-top: calc(var(--sp-5) * 3);
  }
  article {
    --md-block: 0.8em;
    --md-line-height: 1.65;
    --md-h1: 2.2em;
    --md-h2: 1.5em;
    min-width: 0;
    padding-top: calc(var(--sp-5) * 2);
    font-size: var(--fs-lg);
  }
  /* The prose keeps a readable measure; the examples take the width. */
  article > :global(:not(figure)) {
    max-width: 46rem;
  }
  article :global(h2) {
    scroll-margin-top: calc(var(--btn) + var(--sp-5) * 2);
    padding-bottom: var(--sp-2);
    border-bottom: 1px solid var(--border);
  }
  .lede {
    font-size: 1.1em;
    color: var(--color2);
  }
  dt {
    margin-top: var(--sp-3);
    font-weight: 600;
  }
  dd {
    margin-left: var(--md-indent);
  }
  @media (max-width: 1000px) {
    .layout {
      grid-template-columns: minmax(0, 1fr);
      padding: 0 var(--sp-5) calc(var(--sp-5) * 3);
    }
    .toc {
      display: none;
    }
  }
</style>
