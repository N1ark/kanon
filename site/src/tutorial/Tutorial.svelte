<script lang="ts">
  // The tutorial: what Kanon is, then a tiny language built step by step, with the code that
  // Kanon generates from each step.
  import { Callout, Heading, Kbd } from "purr";
  import { Flask } from "purr/icons";
  import Code from "../components/Code.svelte";
  import DocPage from "../components/DocPage.svelte";
  import Example from "./Example.svelte";
</script>

<DocPage page="tutorial">
  <h1>Kanon</h1>
  <p class="lede">
    Kanon is a rule language for the <em>simplifying smart constructors</em> of a value language:
    the functions that build its terms (<code>b_and a b</code>, <code>plus a b</code>, …) and
    simplify them on the fly. You declare the language and write the rules; Kanon generates their
    OCaml implementation and a Lean model of them, with one soundness statement per rule and the
    proof that the whole simplifier is sound from the proofs of these statements.
  </p>
  <p>From the declaration of a language and its rules, the <code>kanon</code> tool generates:</p>
  <ul>
    <li>the OCaml types of the language, with its hash-consed terms;</li>
    <li>the OCaml implementation of the rules, the smart constructors;</li>
    <li>OCaml differential tests of the rule functions;</li>
    <li>
      a Lean model of the rules, with one soundness statement per rule, and the proof that the
      whole simplifier is sound from the proofs of these statements.
    </li>
  </ul>
  <p>
    The value language (its types, nodes, literals, operators and their laws) is declared in
    <code>.knl</code> files: Kanon does not hard-code any. The targets are fixed: OCaml, where
    terms are hash-consed records <code>{"{ kind; ty; tag }"}</code>, and Lean, where they are
    <code>Term.mk kind ty</code>. Kanon is a small, pure, first-order language with its own typing;
    its syntax is that of OCaml, apart from its declarations and the names of rules.
  </p>
  <Callout tone="info" title="Live examples">
    {#snippet icon()}<Flask />{/snippet}
    This tutorial builds a tiny language of booleans and integers, step by step. The code next to
    each step is generated in your browser, by Kanon compiled to JavaScript, and every step opens
    in the <a href="sandbox.html">sandbox</a>, an editor with Kanon's language server. The
    <a href="reference.html">reference</a> lists the declarations, attributes and operators.
  </Callout>

  <Heading level={2} id="declare">Declaring a language</Heading>
  <p>
    A language is declared in <code>.knl</code> files. Its types are those of its OCaml AST, and
    <code>t</code> is the type of its terms: its constructors are the <em>kinds</em> of terms.
    <code>int</code> (arbitrary precision, <code>Z.t</code> in OCaml), <code>bool</code>,
    <code>unit</code>, tuples, <code>option</code> and <code>list</code> are built in.
  </p>
  <Code
    code={`type var [@ocaml "string"] [@lean "String"]

type t =
  | Var of var
  | Unop of unop * t [@operators]
  | Binop of binop * t * t [@operators]`}
  />
  <ul>
    <li>
      <code>var</code> is abstract: <code>[@ocaml "..."]</code> and <code>[@lean "..."]</code> give
      its OCaml and Lean types.
    </li>
    <li>
      <code>[@operators]</code> on a constructor of <code>t</code>: the constructors of the type of
      its first argument are node constructors too, <code>Plus (l, r)</code> standing for
      <code>Binop (Plus, l, r)</code>.
    </li>
  </ul>
  <p>
    A <code>node</code> declares a constructor of terms, with its arguments and its
    <em>typing</em>: the sorts of its operands, then of its result. A <code>sort</code> declares a
    type of terms, a constructor of <code>ty</code>. Kanon places each node in the types of the
    language: an operator on one or two terms in <code>unop</code> or <code>binop</code> (the types
    of the operators of the <code>[@operators]</code> constructors with that many terms), and the
    other nodes in <code>t</code>.
    A type that only has nodes is declared without constructors (<code>type binop</code>), and
    <code>ty</code>, which only has sorts here, need not be declared.
  </p>
  <Code
    code={`node Bool of bool : TBool [@literal]
node Int of int : TInt [@literal int]
node Not : TBool -> TBool
node Eq : a -> a -> TBool

sort TBool
sort TInt`}
  />
  <ul>
    <li>
      <code>Eq</code> has two operands of the same sort <code>a</code>, a variable that stands for
      any sort, and a boolean result. Kanon generates the typing of each node in Lean.
    </li>
    <li>
      <code>[@literal]</code> marks the node of the boolean literals, and
      <code>[@literal int]</code> that of the integer literals. They give the literal patterns:
      <code>true</code> and <code>false</code> match boolean literals, <code>0</code>,
      <code>1</code>, … integer literals, and <code>#x</code> any integer literal, binding
      <code>x</code> to its integer. <code>Plus (x, 0)</code> is thus
      <code>Plus (x, Int 0)</code>.
    </li>
  </ul>
  <p>
    This is enough for the backends that only need the declarations: the OCaml types
    (<code>ocaml-types</code>), and the Lean types and syntax.
  </p>
  <Example id="declare" ocaml="ocaml-types" lean="lean-types" />

  <Heading level={2} id="laws">Operators and laws</Heading>
  <p>
    Attributes on a node declare its algebraic laws, from which Kanon derives the first rules of
    its <em>rule function</em> (the function whose spec is the node over its parameters), before
    the rules written by hand. The derived rules are ordinary rules: they are generated and proved
    like the others.
  </p>
  <Code
    code={`node Not : TBool -> TBool [@invol] [@fold negb]
node And : TBool -> TBool -> TBool [@comm] [@idem] [@unit true] [@zero false]
node Plus : TInt -> TInt -> TInt [@comm] [@unit 0] [@fold add]`}
  />
  <table>
    <thead>
      <tr><th>Law</th><th>Derived rule</th></tr>
    </thead>
    <tbody>
      <tr>
        <td><code>[@comm]</code></td>
        <td>none: the operands commute, and the rules match them in either order</td>
      </tr>
      <tr>
        <td><code>[@fold f]</code></td>
        <td>
          <code>lits: Int i1 + Int i2 -> Int (add i1 i2)</code>,
          <code>lit: Bool b -> Bool (negb b)</code>
        </td>
      </tr>
      <tr><td><code>[@unit c]</code></td><td><code>zero: x + 0 -> x</code></td></tr>
      <tr><td><code>[@zero c]</code></td><td><code>false_: _ &amp;&amp; false -> Bool false</code></td></tr>
      <tr><td><code>[@idem]</code></td><td><code>same: v &amp;&amp; v -> v</code></td></tr>
      <tr>
        <td><code>[@invol]</code></td>
        <td><code>not: not x -> x</code>, named after the operator (unary operators)</td>
      </tr>
    </tbody>
  </table>
  <p>
    <code>[@fold f]</code> folds literals with the function <code>f</code>, and makes a term of
    its result with the literal node of its type: <code>Bool</code> for a <code>bool</code>,
    <code>Int</code> for an <code>int</code> (<code>[@fold f lift]</code> names another function
    or node). <code>[@unit c]</code> and <code>[@zero c]</code> take the literal <code>0</code>,
    <code>1</code>, <code>true</code> or <code>false</code>; <code>[@zero false]</code> builds the
    literal <code>Bool false</code>, unless the language gives another term for it, with the
    optional <code>constant "false" = e</code>.
  </p>
  <p>
    Operators give a syntax to nodes. <code>infix "op" = Node, f</code> declares what
    <code>a op b</code> builds and matches: in expressions, it calls the smart constructor
    <code>f</code>; in patterns, it matches the node. An operator is a word, or a sequence of
    symbols such as <code>+</code>, <code>==</code> or <code>≤</code>, whose first character gives
    its precedence, as in OCaml (see the <a href="reference.html#operators">reference</a>).
  </p>
  <Code
    code={`infix "&&" = And, and_
infix "+" = Plus, plus
infix "==" = Eq, eq
prefix "not" = Not, not_`}
  />
  <p>
    The rules are in <code>.kn</code> files, which the language uses (<code>use "rules"</code>
    reads <code>rules.knl</code> and <code>rules.kn</code>, either of which may be missing). A rule
    function without a body, <code>rule f : spec</code>, only has the rules derived from the laws
    of its spec, and <code>default</code>, which builds the spec. <code>fn</code> declares a
    helper, here the functions of the folds.
  </p>
  <Code
    code={`fn negb (b : bool) : bool = not b
fn add (x y : int) : int = x + y

rule not_ : Not v
rule and_ : And (v1, v2)
rule plus : Plus (v1, v2)`}
  />
  <p>
    The generated <code>and_</code> tries the rules of the laws in order, each in both orders of the
    operands, and the Lean statements say that each of them refines its spec.
  </p>
  <Example id="laws" ocaml="ocaml" lean="lean-statements" />
  <p>
    When no rule applies, <code>and_ v1 v2</code> builds its spec with
    <code>mk_commut_binop And v1 v2</code>, which puts the operands of a commutative operator in a
    normal order, the one with the smaller hash-consing tag on the left: <code>a &amp;&amp; b</code>
    and <code>b &amp;&amp; a</code> are then the same term.
  </p>

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
  | assoc: (x + #a) + #b -> x + Int (a + b)

rule eq : Eq (v1, v2) =
  | same: x == x -> Bool true
  | lits: #x == #y -> Bool (x = y)
  | true_: true == x -> x
  | neg: #x == y when x < 0 && is_nat y -> Bool false`}
  />
  <ul>
    <li>
      Patterns match the kind of a term directly, with the literal patterns (<code>true</code>,
      <code>0</code>, <code>#x</code>) of the <code>[@literal]</code> nodes.
    </li>
    <li>
      In expressions, <code>x + Int (a + b)</code> calls the smart constructor <code>plus</code>
      again, and <code>a + b</code> on integers is the sum of integers. Nodes build raw terms,
      without simplification: <code>Int (a + b)</code>, <code>Bool true</code>.
    </li>
    <li>
      A repeated variable matches equal terms: <code>x == x</code>. On terms, <code>=</code> is the
      equality of hash-consed terms.
    </li>
    <li>
      The spec <code>Eq (v1, v2)</code> is commutative: the cases match its operands in either
      order, unless the pattern is symmetric. The cases must then name the operands rather than use
      <code>v1</code> and <code>v2</code>. The operands of commutative operators in patterns match
      in either order too: <code>x + #a</code> also matches <code>#a + x</code>.
    </li>
    <li>
      <code>when</code> guards, or-patterns, <code>as</code>, <code>Some</code>/<code>None</code>,
      lists and partial records are supported. A case that an earlier case without a guard already
      matches can never be taken: Kanon leaves it out.
    </li>
  </ul>
  <p>
    Helpers are functions, <code>fn f params : ty = body</code>; all functions can call each other.
    <code>prim f : a -> b</code> declares a primitive, implemented by hand in OCaml, in the module
    that <code>[@@@ocaml_prims "Prims"]</code> names, and in Lean. <code>oracle f : a -> b</code>
    declares one that the Lean model takes as a parameter, so that the proofs may not rely on its
    behaviour (e.g. a hash-consing order).
  </p>
  <Code
    code={`prim var_is_nat : var -> bool

(* Whether a term is surely a natural number. *)
fn is_nat (v : t) : bool =
  match v with
  | Int n -> n >= 0
  | Var x -> var_is_nat x
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

type t =
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
    the files, at the precedence of comparisons, and no longer a name.
  </p>
  <Example id="modules" ocaml="ocaml" lean="lean-soundness" />

  <Heading level={2} id="typings">Typings</Heading>
  <p>
    Sorts may have arguments, and the typing of a node may name its arguments and constrain them
    with a condition. With arrays of a length:
  </p>
  <Code
    code={`sort TArray of nat [@get length]

node Get of nat (i) : TArray n -> TInt when i < n
node Concat : TArray n -> TArray m -> TArray (n + m)`}
  />
  <ul>
    <li>
      <code>Get (i, a)</code> reads the element <code>i</code> of the array <code>a</code>, of sort
      <code>TArray n</code> for any <code>n</code>, under the condition <code>i &lt; n</code>. A
      <code>nat</code> argument is an OCaml <code>int</code> and a Kanon <code>int</code>.
    </li>
    <li>
      Nodes build terms at the sort that their typing infers: <code>Concat (l, r)</code> has the
      sort <code>TArray (n + m)</code>, from the sorts of <code>l</code> and <code>r</code>.
    </li>
    <li>
      <code>[@get length]</code>: the helper <code>length</code> reads the argument of the sort of a
      term, which Kanon then calls rather than matching the sort.
    </li>
    <li>
      An operand of a spec may be annotated with its sort, to bind its variables in the rules:
      <code>rule get : Get (i, (a : TArray n))</code> uses <code>n</code>.
    </li>
  </ul>
  <p>
    Soteria's symbolic values, with bit-vectors whose literals have an abstract type
    (<code>[@literal t]</code>, see the <a href="reference.html#on-constructors">reference</a>),
    are written in Kanon.
  </p>

  <Heading level={2} id="generated">What Kanon generates</Heading>
  <p>
    <code>kanon BACKEND FILE...</code> reads the language declared by the files, usually its one
    <code>.knl</code> file, and writes on standard output:
  </p>
  <dl>
    <dt><code>ocaml-types</code></dt>
    <dd>
      the types of the language and its terms, hash-consed records
      <code>{"{ kind; ty; tag }"}</code> (<code>kind</code> has the constructors of
      <code>t</code>), as a standalone OCaml file that only needs Zarith;
    </dd>
    <dt><code>ocaml</code></dt>
    <dd>
      the rule functions and helpers, which call the primitives in the module of
      <code>[@@@ocaml_prims]</code>. They need the types in scope: included next to them (the ppx
      <code>kanon.ppx_include_file</code> includes a file: <code>[%%include_file "rules.gen.ml"]</code>),
      or in the module of <code>[@@@ocaml_types "M"]</code>, which they open;
    </dd>
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
    hash-consing order. <code>ocaml-check</code>, the check of the OCaml types of a language
    against hand-written ones, is deprecated. The <a href="sandbox.html">sandbox</a> shows every
    backend on your own files.
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
    gives the tactics <code>kanon_auto</code>, the default proof of an alternative (an
    <em>arm</em>), and <code>kanon_congr</code>, refinement by congruence; an arm that
    <code>kanon_auto</code> does not prove gets a theorem tagged <code>@[kanon_arm]</code>. Kanon's
    Lean library (<code>lean/</code>, the package <code>kanon</code>) gives what does not depend on
    the language.
  </p>
  <p>
    A rule over commutative operators has an arm for each swap of their operands. Kanon states once
    that each <code>[@comm]</code> operator commutes (<code>Binop.Plus.comm.Stmt</code>, proved by
    <code>kanon_auto</code> or by hand), and proves from it, with <code>kanon_congr</code> for the
    operands swapped below the spec, every arm that only swaps operands, if its guard and body do
    not depend on the swap. The proofs to write are thus one per case of a rule, when
    <code>kanon_auto</code> does not find it, and one per commutative operator.
  </p>
  <p>
    <code>examples/bool/</code> is a complete example: the bool module alone, with its Lean proof
    in <code>lean/</code>. Its semantics has booleans as values and <code>none</code> as poison;
    the rules of the bool module are proved once, for any language that uses it, by Kanon's Lean
    library. To check it:
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
</DocPage>

<style>
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
</style>
