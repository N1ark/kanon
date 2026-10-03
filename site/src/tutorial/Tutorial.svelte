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
    the functions that build its terms (<code>{`b_and a b{:kanon}`}</code>,
    <code>{`plus a b{:kanon}`}</code>, …) and simplify them on the fly. You declare the language and
    write the rules; Kanon generates their OCaml implementation and a Lean model of them, with one
    soundness statement per rule and the proof that the whole simplifier is sound from the proofs of
    these statements.
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
    <code>.knl</code> files: Kanon does not hard-code any. The targets are fixed: OCaml, where terms
    are hash-consed records <code>{`{ kind; ty; tag }{:ocaml}`}</code>, and Lean, where they are
    <code>{`Term.mk kind ty{:lean}`}</code>. Kanon is a small, pure, first-order language with its
    own typing; its syntax is that of OCaml, apart from its declarations and the names of rules.
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
    A language is declared in <code>.knl</code> files. A <code>node</code> declares a constructor of
    its terms, with its arguments and its <em>typing</em>: the sorts of its operands, then of its
    result. A <code>sort</code> declares a type of terms. <code>type</code> declares the other
    types, here the abstract type of variables, whose OCaml and Lean types
    <code>{`[@ocaml "..."]{:kanon}`}</code> and <code>{`[@lean "..."]{:kanon}`}</code> give.
    <code>int</code> (arbitrary precision, <code>Z.t</code> in OCaml), <code>bool</code>,
    <code>unit</code>, tuples, <code>option</code> and <code>list</code> are built in.
  </p>
  <Code
    code={`type var [@ocaml "string"] [@lean "String"]

(** A variable. *)
node Var of var
(** A boolean literal. *)
node Bool of bool : TBool
(** An integer literal. *)
node Int of int : TInt
(** Negation. *)
node Not : TBool -> TBool
(** Conjunction. *)
node And : TBool -> TBool -> TBool
(** The sum of two integers. *)
node Plus : TInt -> TInt -> TInt
(** Equality of two terms of any sort. *)
node Eq : a -> a -> TBool

(** The sort of booleans. *)
sort TBool
(** The sort of integers. *)
sort TInt

notation Bool
notation Int`}
  />
  <ul>
    <li>
      A documentation comment <code>(** … *)</code> right before a declaration documents it:
      Kanon copies it to the generated OCaml (as <code>(** … *)</code>) and Lean (as
      <code>/-- … -/</code>), next to the constructor or the function. A plain comment
      <code>(* … *)</code> is ignored.
    </li>
    <li>
      <code>Var</code>, <code>Bool</code> and <code>Int</code> have no operands: they are the
      leaves of terms. <code>Not</code>, <code>And</code>, <code>Plus</code> and <code>Eq</code> are
      operators, of one and two operands.
    </li>
    <li>
      <code>Eq</code> has two operands of the same sort <code>a</code>, a variable that stands for
      any sort, and a boolean result. Kanon generates the typing of each node in Lean.
    </li>
    <li>
      <code>{`notation Bool{:kanon}`}</code> and <code>{`notation Int{:kanon}`}</code> give the
      literal patterns of these leaves, a sugar of patterns: <code>true</code> and
      <code>false</code> stand for <code>{`Bool true{:kanon}`}</code> and
      <code>{`Bool false{:kanon}`}</code>, the numerals <code>0</code>, <code>1</code>,
      <code>-1</code>, … for <code>{`Int 0{:kanon}`}</code>, …, <code>#x</code> for
      <code>{`Int x{:kanon}`}</code> or <code>{`Bool x{:kanon}`}</code>, binding <code>x</code> to
      the integer or the boolean, and <code>#_</code> for <code>{`Int _{:kanon}`}</code> or
      <code>{`Bool _{:kanon}`}</code>. <code>{`Plus (x, 0){:kanon}`}</code> is thus
      <code>{`Plus (x, Int 0){:kanon}`}</code>.
    </li>
    <li>
      Kanon resolves a literal by its kind (a numeral is an <code>Int</code>), then by the sort of
      its position: <code>#x</code> is an <code>Int</code> as an operand of <code>Plus</code>.
      Where neither decides, as for <code>#x</code> as an operand of <code>Eq</code>, of any sort,
      the rule names the node: <code>{`Int x{:kanon}`}</code>.
    </li>
  </ul>
  <p>
    Kanon generates the types of the terms from the nodes and the sorts: in OCaml, the leaves are
    constructors of the terms, and the operators of one and two operands constructors of the types
    <code>op1</code> and <code>op2</code>, under the constructors
    <code>{`Op1 of op1 * t{:ocaml}`}</code> and <code>{`Op2 of op2 * t * t{:ocaml}`}</code>. Rules
    never name these: they write <code>{`And (a, b){:kanon}`}</code>. This is enough for the
    backends that only need the declarations: the OCaml types (<code>ocaml-types</code>), and the
    Lean types and syntax.
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
      <tr><th>Law</th><th>Rule</th><th>Rewrite</th></tr>
    </thead>
    <tbody>
      <tr>
        <td><code>{`[@comm]{:kanon}`}</code></td>
        <td>none</td>
        <td>the operands commute: the rules match them in either order</td>
      </tr>
      <tr>
        <td><code>{`[@fold f]{:kanon}`}</code></td>
        <td><code>lits</code>, <code>lit</code></td>
        <td>
          <code>{`Int i1 + Int i2 -> Int (add i1 i2){:kanon}`}</code>,
          <code>{`not (Bool b) -> Bool (negb b){:kanon}`}</code>
        </td>
      </tr>
      <tr>
        <td><code>{`[@unit c]{:kanon}`}</code></td>
        <td><code>unit_zero</code>, <code>unit_true</code></td>
        <td><code>{`x + 0 -> x{:kanon}`}</code>, <code>{`x && true -> x{:kanon}`}</code></td>
      </tr>
      <tr>
        <td><code>{`[@zero c]{:kanon}`}</code></td>
        <td><code>zero_false</code></td>
        <td><code>{`x && false -> false{:kanon}`}</code></td>
      </tr>
      <tr>
        <td><code>{`[@idem]{:kanon}`}</code></td>
        <td><code>same</code></td>
        <td><code>{`x && x -> x{:kanon}`}</code></td>
      </tr>
      <tr>
        <td><code>{`[@invol]{:kanon}`}</code></td>
        <td><code>not</code>, after the operator</td>
        <td><code>{`not (not x) -> x{:kanon}`}</code></td>
      </tr>
    </tbody>
  </table>
  <p>
    The rewrites are on whole terms: in <code>{`rule not_ : Not v{:kanon}`}</code>, the case of
    <code>{`[@invol]{:kanon}`}</code> is <code>{`not x -> x{:kanon}`}</code>, on the operand
    <code>v</code>. <code>{`[@fold f]{:kanon}`}</code> folds literals with the function
    <code>f</code>, and makes a term of its result with the notation of its type: <code>Bool</code>
    for a <code>bool</code>, <code>Int</code> for an <code>int</code>
    (<code>{`[@fold f lift]{:kanon}`}</code> names another function or node).
    <code>{`[@unit c]{:kanon}`}</code> and <code>{`[@zero c]{:kanon}`}</code> take the literal
    <code>0</code>, <code>1</code>, <code>true</code> or <code>false</code>, or a named constant;
    <code>{`[@zero false]{:kanon}`}</code> builds the literal <code>{`Bool false{:kanon}`}</code>,
    unless the language gives another term for it, with the optional
    <code>{`constant false = e{:kanon}`}</code>.
  </p>
  <p>
    Operators give a syntax to nodes. <code>{`infix "op" = Node, f{:kanon}`}</code> declares what
    <code>a op b</code> builds and matches: in expressions, it calls the smart constructor
    <code>f</code>; in patterns, it matches the node. An operator is a word, or a sequence of
    symbols such as <code>+</code>, <code>==</code> or <code>≤</code>, possibly followed by a word
    (<code>&lt;u</code>), whose first character gives its precedence, as in OCaml (see the
    <a href="reference.html#operators">reference</a>). Operators are surrounded by spaces:
    <code>{`a <u b{:kanon}`}</code> and <code>{`x + y{:kanon}`}</code>, but <code>{`x+y{:kanon}`}</code>
    is an error, not <code>{`x + y{:kanon}`}</code>. Only a prefix operator is written right before
    its operand: <code>{`-x{:kanon}`}</code>, <code>{`~x{:kanon}`}</code>.
  </p>
  <Code
    code={`infix "&&" = And, and_
infix "+" = Plus, plus
infix "==" = Eq, eq
prefix "not" = Not, not_`}
  />
  <p>
    The rules are in <code>.kn</code> files, which the language uses
    (<code>{`use "rules"{:kanon}`}</code> reads <code>rules.knl</code> and <code>rules.kn</code>,
    either of which may be missing). A rule function without a body,
    <code>{`rule f : spec{:kanon}`}</code>, only has the rules derived from the laws of its spec,
    and <code>default</code>, which builds the spec. <code>fn</code> declares a helper, here the
    functions of the folds.
  </p>
  <Code
    code={`(** Negation of a boolean. *)
fn negb (b : bool) : bool = not b

(** Sum of two integers. *)
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
    When no rule applies, <code>{`and_ v1 v2{:kanon}`}</code> builds its spec with
    <code>{`mk_commut_binop And v1 v2{:kanon}`}</code>, which puts the operands of a commutative
    operator in a normal order, the one with the smaller hash-consing tag on the left:
    <code>{`a && b{:kanon}`}</code> and <code>{`b && a{:kanon}`}</code> are then the same term.
  </p>

  <Heading level={2} id="rules">Rules</Heading>
  <p>
    <code>{`rule f : e = | r: p -> body | ...{:kanon}`}</code> declares a rule function, which
    returns a term that must <em>refine</em> the raw term <code>e</code>, its spec. When the spec is
    a node over variables, they are the parameters of the function. Its cases match the operands of
    the spec (as a tuple when there are several), and each is a rule, named by the label before its
    pattern; rules are tried in order. Unless its last case matches anything (<code>_</code>, or
    <code>{`_, _{:kanon}`}</code> for two operands: the two are the same), a rule function ends with
    the rule <code>default</code>, which builds its spec.
  </p>
  <Code
    code={`(** Sum: adjacent literals are added. *)
rule plus : Plus (v1, v2) =
  | assoc: (x + #a) + #b -> x + Int (a + b)

(** Equality: literals are compared, and a negative literal differs from a natural number. *)
rule eq : Eq (v1, v2) =
  | same: x == x -> Bool true
  | lits: Int x == Int y -> Bool (x = y)
  | true_: true == x -> x
  | neg: Int x == y when x < 0 && is_nat y -> Bool false`}
  />
  <ul>
    <li>
      Patterns match the kind of a term directly, with the literal patterns (<code>true</code>,
      <code>0</code>, <code>#x</code>) of the notations.
    </li>
    <li>
      In expressions, <code>{`x + Int (a + b){:kanon}`}</code> calls the smart constructor
      <code>plus</code> again, and <code>{`a + b{:kanon}`}</code> on integers is the sum of
      integers. Nodes build raw terms, without simplification: <code>{`Int (a + b){:kanon}`}</code>,
      <code>{`Bool true{:kanon}`}</code>.
    </li>
    <li>
      A repeated variable matches equal terms: <code>{`x == x{:kanon}`}</code>. On terms,
      <code>=</code> is the equality of hash-consed terms.
    </li>
    <li>
      The spec <code>{`Eq (v1, v2){:kanon}`}</code> is commutative: the cases match its operands in
      either order, unless the pattern is symmetric. The cases must then name the operands rather
      than use <code>v1</code> and <code>v2</code>. The operands of commutative operators in
      patterns match in either order too: <code>{`x + #a{:kanon}`}</code> also matches
      <code>{`#a + x{:kanon}`}</code>.
    </li>
    <li>
      <code>when</code> guards, or-patterns, <code>as</code>, <code>Some</code>/<code>None</code>,
      lists and partial records are supported. A case that an earlier case without a guard already
      matches can never be taken: Kanon leaves it out.
    </li>
  </ul>
  <p>
    Helpers are functions, <code>fn f params : ty = body</code>; all functions can call each other.
    <code>{`prim f : a -> b{:kanon}`}</code> declares a primitive, implemented by hand in OCaml, in
    the module that <code>{`[@@@ocaml_prims "Prims"]{:kanon}`}</code> names, and in Lean.
    <code>{`oracle f : a -> b{:kanon}`}</code> declares one that the Lean model takes as a
    parameter, so that the proofs may not rely on its behaviour (e.g. a hash-consing order).
  </p>
  <Code
    code={`(** Whether a variable is surely a natural number. *)
prim var_is_nat : var -> bool

(** Whether a term is surely a natural number. *)
fn is_nat (v : t) : bool =
  match v with
  | Int n -> n >= 0
  | Var x -> var_is_nat x
  | l + r -> is_nat l && is_nat r
  | _ -> false`}
  />
  <p>
    In the Lean model, every rule is a function to <code>{`Option Term{:lean}`}</code>, and a rule
    function the first of its rules that applies:
  </p>
  <p>
    A helper or a primitive that the Lean model should not contain, such as a heuristic that only
    the OCaml code uses, is marked <code>{`[@no_lean]{:kanon}`}</code>: it is generated in OCaml and
    left out of every Lean file. A function that is modelled may not call it, so the proofs never
    depend on it; it may call anything. Rules, sorts, nodes and oracles cannot be marked: they are
    proved. Below, <code>cost</code> is in the OCaml and not in the Lean.
  </p>
  <Code
    code={`(** A size estimate, for the OCaml code around the simplifier: not modelled in Lean. *)
fn cost (v : t) : int [@no_lean] =
  match v with
  | l + r -> cost l + cost r + 1
  | _ -> 1`}
  />
  <Example id="rules" ocaml="ocaml" lean="lean-model" />

  <Heading level={2} id="modules">Modules</Heading>
  <p>
    A language is made of the modules it uses, each with its declarations (<code>int.knl</code>) and
    its rules, primitives and helpers (<code>int.kn</code>). <code>{`use "path"{:kanon}`}</code>
    uses a module relative to the file, and <code>{`use builtin "bool"{:kanon}`}</code> the module
    of booleans built into <code>kanon</code>: boolean literals, <code>Not</code>, <code>And</code>,
    <code>Or</code>, equality (<code>Eq</code>), conditionals (<code>Ite</code>) and
    <code>Distinct</code>, with their rules (all of it in the
    <a href="sandbox.html#example=builtin-bool">sandbox</a>). The language adds its own nodes, here
    its variables.
  </p>
  <Code
    code={`[@@@ocaml_prims "Prims"]

use builtin "bool"
use "int"

type var [@ocaml "string"] [@lean "String"]

node Var of var`}
  />
  <p>
    <code>Distinct</code>, of the bool module, has any number of operands, of the same sort:
    <code>{`node Distinct : a list -> TBool{:kanon}`}</code>. The bool module has primitives, whose
    OCaml module <code>{`[@@@ocaml_prims]{:kanon}`}</code> names.
  </p>
  <p>
    A module adds rules to the rule function of a module below it with
    <code>extend rule f</code>: last, but before its final catch-all case (<code>_</code>, or
    <code>{`_, _{:kanon}`}</code>, a tuple of blanks, for the operands of a spec or a helper), or
    before its rule <code>r</code> with <code>extend rule f before r</code>. <code>extend fn</code> adds cases to a
    helper, here the literals of <code>int</code> to the bool module's <code>sure_neq</code>. A case that an
    earlier case already matches is an error there, rather than left out.
  </p>
  <Code
    code={`extend rule sem_eq before same =
  | ints: Int x == Int y -> of_bool (x = y)

extend fn sure_neq =
  | Int x, Int y -> not (x = y)`}
  />
  <p>
    A word declared as an operator, like <code>lt</code> below, is an infix operator in the rest of
    the files, at the precedence of <code>*</code>, and no longer a name.
  </p>
  <Example id="modules" ocaml="ocaml" lean="lean-soundness" />

  <Heading level={2} id="typed">Subsorts</Heading>
  <p>
    The generated OCaml functions take and return terms of one type, <code>t</code>: nothing stops
    <code>plus</code> from being applied to a boolean (the assertions on entry catch it at run
    time). <code>ocaml-typed</code> generates an OCaml <em>interface</em> of the smart constructors
    instead, where a term is typed by a <em>ghost tag</em>, a polymorphic variant that says what
    Kanon knows of it, and the OCaml compiler rejects the ill-kinded calls. The tag of a term is
    that of its sort, which Kanon generates, and a <em>subsort</em> refines it.
  </p>
  <Code
    code={`sort TInt
subsort TNonzero : TInt

node Int of int : TInt [@ctor mk_int]
node Div : TInt -> TNonzero -> TInt`}
  />
  <ul>
    <li>
      <code>{`subsort TNonzero : TInt{:kanon}`}</code> declares a sort of the terms of
      <code>TInt</code> that satisfy more than that: here that they are not zero. A subsort has the
      arguments of its parent, none here (<code>{`subsort TNonzero of nat : TBitVector n{:kanon}`}</code>
      for a width). A node may use it in its typing: the divisor of <code>Div</code> is a
      <code>TNonzero</code>. A term of a subsort is accepted wherever its parent is expected, and
      not the reverse.
    </li>
    <li>
      A subsort has no meaning in OCaml, where the types and the rules erase it to its parent: it
      is trusted. Only the interface uses it, with the tags <code>tint</code> and
      <code>tnonzero</code>, and Lean can give it a meaning (see the
      <a href="reference.html#declarations">reference</a>).
    </li>
    <li>
      A leaf, or a node without a rule function, has a function in the interface only with
      <code>{`[@ctor f]{:kanon}`}</code>: <code>mk_int</code> builds an integer literal.
    </li>
  </ul>
  <Example id="typed" ocaml="ocaml-typed" lean="lean-model" />
  <p>
    <code>[&lt; tint ] t</code>, as an operand, accepts any term whose tag is within
    <code>tint</code>, which includes <code>tnonzero</code>, and <code>[&gt; tint ] t</code>, as a
    result, is a term that may have any of them. The module <code>Ghost</code> implements the phantom
    types of the interface, and the rules implement the rest, so that the implementation is
    <code>{`struct include Ghost include Rules let mk_int = ... end{:ocaml}`}</code>, which OCaml
    checks against the interface. A client of the interface then cannot add an integer to a
    boolean:
  </p>
  <Code
    lang="ocaml"
    code={`plus (mk_int Z.one) (int_lt (mk_int Z.one) (mk_int Z.zero))`}
  />
  <Code
    lang="text"
    code={`Error: This expression has type [> Tag.tbool ] t
       but an expression was expected of type [< Tag.tint ] t
       …
       The second variant type does not allow tag(s) \`TBool`}
  />
  <p>
    The same goes for a divisor that is not known to be non-zero:
    <code>{`div (mk_int Z.one) (mk_int Z.one){:ocaml}`}</code> is rejected too, since the result of
    <code>mk_int</code> is any <code>tint</code>. A caller that knows better says so with
    <code>cast</code>, which is the identity at run time (and so are <code>untyped</code> and
    <code>type_</code>): the subsort is trusted, nothing proves it.
  </p>

  <Heading level={2} id="typings">Typings</Heading>
  <p>
    Sorts may have arguments, and the typing of a node may name its arguments and constrain them
    with a condition. With arrays of a length:
  </p>
  <Code
    code={`sort TArray of nat [@get length]

node Get of nat (i) : TArray n -> TInt when i < n
node Concat : TArray n -> TArray m -> TArray (n + m)
node Fill of int : TArray n`}
  />
  <ul>
    <li>
      <code>{`Get (i, a){:kanon}`}</code> reads the element <code>i</code> of the array
      <code>a</code>, of sort <code>{`TArray n{:kanon}`}</code> for any <code>n</code>, under the
      condition <code>{`i < n{:kanon}`}</code>. A <code>nat</code> argument is an OCaml
      <code>int</code> and a Kanon <code>int</code>.
    </li>
    <li>
      Nodes build terms at the sort that their typing infers: <code>{`Concat (l, r){:kanon}`}</code>
      has the sort <code>{`TArray (n + m){:kanon}`}</code>, from the sorts of <code>l</code> and
      <code>r</code>. The sort of <code>{`Fill z{:kanon}`}</code>, an array of <code>z</code>s, is
      not determined by its argument: it is built at an explicit sort,
      <code>{`(Fill z : TArray n){:kanon}`}</code>.
    </li>
    <li>
      <code>{`[@get length]{:kanon}`}</code>: the helper <code>length</code> reads the argument of
      the sort of a term, which Kanon then calls rather than matching the sort.
    </li>
    <li>
      An operand of a spec, or a parameter of a helper, may be annotated with its sort, to bind its
      variables: <code>{`rule get : Get (i, (a : TArray n)){:kanon}`}</code> and
      <code>{`fn last (a : TArray n) : t = Get (n - 1, a){:kanon}`}</code> use <code>n</code>. The
      generated OCaml asserts the sort on entry.
    </li>
  </ul>
  <p>
    Soteria's symbolic values, with bit-vectors whose width is in their sort, are written in
    Kanon (see the <a href="reference.html#notation">reference</a>).
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
      <code>{`{ kind; ty; tag }{:ocaml}`}</code> (<code>kind</code> has the leaves and the
      <code>Op1</code>, <code>Op2</code>, … of the operators, <code>ty</code> the sorts), as a
      standalone OCaml file that only needs Zarith. Its table of hash-consing is not safe to use
      from several OCaml 5 domains at once (a known limitation);
    </dd>
    <dt><code>ocaml</code></dt>
    <dd>
      the rule functions and helpers, which call the primitives in the module of
      <code>{`[@@@ocaml_prims]{:kanon}`}</code>. They need the types in scope: included next to them
      (the ppx <code>kanon.ppx_include_file</code> includes a file:
      <code>{`[%%include_file "rules.gen.ml"]{:ocaml}`}</code>), or in the module of
      <code>{`[@@@ocaml_types "M"]{:kanon}`}</code>, which they open;
    </dd>
    <dt><code>ocaml-typed</code></dt>
    <dd>
      the interface of the smart constructors, typed by the tags of the sorts and subsorts (see
      <a href="#typed">Subsorts</a>): a <code>module type S</code>, and <code>Ghost</code>, which
      implements its phantom types;
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
    hash-consing order. The <a href="sandbox.html">sandbox</a> shows every backend on your own
    files.
  </p>

  <Heading level={2} id="proofs">Proofs</Heading>
  <p>
    The Lean files are generated in the namespace of <code>{`[@@@lean_root "R"]{:kanon}`}</code>
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
    Written by hand, for each language: the abstract types (<code>R.Abstract</code>), the primitives
    (<code>R.Prims</code>), the semantics of terms and the refinement <code>Refines</code>
    (<code>R.Semantics</code>), and the tactics of the proofs. The language gives the tactics
    <code>kanon_auto</code>, the default proof of an alternative (an <em>arm</em>), and
    <code>kanon_congr</code>, refinement by congruence; an arm that <code>kanon_auto</code> does not
    prove gets a theorem tagged <code>{`@[kanon_arm]{:lean}`}</code>. Kanon's Lean library
    (<code>lean/</code>, the package <code>kanon</code>) gives what does not depend on the language.
  </p>
  <p>
    A rule over commutative operators has an arm for each swap of their operands. Kanon states once
    that each <code>{`[@comm]{:kanon}`}</code> operator commutes (<code>Op2.Plus.comm.Stmt</code>,
    proved by <code>kanon_auto</code> or by hand), and proves from it, with <code>kanon_congr</code>
    for the operands swapped below the spec, every arm that only swaps operands, if its guard and
    body do not depend on the swap. The proofs to write are thus one per case of a rule, when
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
  <p>
    The <a href="proving.html">guide to proofs</a> walks through the proof of the language of this
    tutorial, <code>examples/ints/</code>: the files to write, and how to prove the rules.
  </p>
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
