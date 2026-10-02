<script lang="ts">
  // The reference: the declarations, the attributes and the operators of Kanon.
  import { Heading } from "purr";
  import Code from "../components/Code.svelte";
  import DocPage from "../components/DocPage.svelte";

  const README = "https://github.com/N1ark/kanon#readme";
</script>

<DocPage page="reference" headings="h2, h3">
  <h1>Reference</h1>
  <p class="lede">
    The declarations, attributes and operators of Kanon, in brief. The <a href="./">tutorial</a>
    introduces them on an example; the <a href={README}>README</a> details the generated code and
    the proofs.
  </p>

  <Heading level={2} id="declarations">Declarations</Heading>
  <p>
    A language is declared in <code>.knl</code> files, with <code>use</code>, <code>type</code>,
    <code>sort</code>, <code>node</code>, <code>infix</code>, <code>prefix</code> and
    <code>constant</code> items and floating attributes; its rules are in <code>.kn</code> files,
    with <code>prim</code>, <code>oracle</code>, <code>fn</code>, <code>rule</code> and
    <code>extend</code> items. A module <code>path</code> is the pair <code>path.knl</code> and
    <code>path.kn</code>, either of which may be missing.
  </p>
  <dl>
    <dt><code>use "path"</code>, <code>use +name</code></dt>
    <dd>
      Uses the module <code>path</code>, relative to the directory of the file, or the module
      <code>name</code> built into <code>kanon</code> (<code>+bool</code>). A module is read once;
      the declarations of a file come before those of the modules it uses, and its rules after
      theirs.
    </dd>

    <dt><code>type x attrs</code>, <code>type x attrs = | C of a * b | …</code>, <code>type x attrs = {"{ f : a; … }"}</code></dt>
    <dd>
      An abstract, variant or record type, of the arguments of nodes and of the helpers.
      <code>int</code> (arbitrary precision), <code>bool</code>, <code>unit</code>, tuples,
      <code>option</code> and <code>list</code> are built in; <code>nat</code>, in the arguments
      of nodes and sorts, is an OCaml <code>int</code> (a width, an index) and a Kanon
      <code>int</code>. <code>t</code>, the type of terms, and <code>ty</code>, the type of their
      sorts, are generated from the nodes and the sorts, and cannot be declared.
    </dd>

    <dt><code>sort S attrs</code>, <code>sort S of a * b attrs</code></dt>
    <dd>A sort, the type of a term: a constructor of <code>ty</code>.</dd>

    <dt><code>node C of a * b (x, y) : s1 -> s2 -> s when e attrs</code></dt>
    <dd>
      A node: a constructor of terms, with its arguments <code>a * b</code> (named
      <code>x</code>, <code>y</code> in its typing), and its typing, all optional. Its operands, then
      its result, have the sorts <code>s1</code>, <code>s2</code>, <code>s</code>, terms of
      <code>ty</code> over the arguments and over variables, which stand for any sort (or any
      value), under the condition <code>e</code> (see <a href="./#typings">Typings</a>). A node
      without operands (<code>node Var of var</code>) is a leaf; one with <code>k</code> operands
      is an operator of arity <code>k</code>; one whose only operand sort is a list,
      <code>node Distinct : a list -> TBool</code>, an operator of any number of operands, all of
      the sort <code>a</code>.
    </dd>

    <dt><code>infix "op" = Node, f args, g</code>, <code>prefix "op" = Node, f args, g</code></dt>
    <dd>An operator on terms; <code>g</code> is optional (see <a href="#operators">Operators</a>).</dd>

    <dt><code>constant c = e</code>, <code>constant c (v) = e</code></dt>
    <dd>
      The term of the constant <code>c</code>, at the sort of the term <code>v</code>, for the laws
      <code>[@unit c]</code> and <code>[@zero c]</code>. <code>c</code> is a literal
      (<code>0</code>, <code>1</code>, <code>true</code> or <code>false</code>), whose
      <code>constant</code> is optional: Kanon otherwise builds the literal node itself
      (<code>Bool false</code>, <code>Int 0</code>), except for <code>[@literal v]</code>
      literals, whose values are abstract. Or <code>c</code> is a name, such as <code>ones</code>
      for the bit-vector of ones of a width: <code>constant ones (v) = lit_ones (size v)</code>.
    </dd>

    <dt><code>[@@@name "arg" …]</code></dt>
    <dd>A floating attribute (see <a href="#floating">below</a>).</dd>

    <dt><code>prim f : a -> b</code>, <code>oracle f : a -> b</code></dt>
    <dd>
      A primitive, implemented by hand in OCaml (in the module of
      <code>[@@@ocaml_prims]</code>) and in Lean; the generated code checks that both define it, at
      this type. The Lean model takes an oracle as a parameter, so that the proofs may not rely on
      its behaviour (e.g. a hash-consing order).
    </dd>

    <dt><code>fn f (x : a) (y z : b) : c attrs = e</code></dt>
    <dd>A helper. All functions can call each other.</dd>

    <dt><code>rule f params : spec attrs = | r: p -> e | …</code>, <code>… = e</code>, <code>rule f params : spec attrs</code></dt>
    <dd>
      A rule function: it returns a term that refines the raw term <code>spec</code>. Its cases
      match the operands of the spec and are its rules, named by their labels, tried in order after
      the rules derived from the laws of the spec; it ends with the rule <code>default</code>,
      which builds the spec, unless its last case matches anything. When the spec is a node over
      variables, they are its parameters.
    </dd>

    <dt><code>extend rule f before r = | r': p -> e | …</code>, <code>extend fn f = | p -> e | …</code></dt>
    <dd>
      Adds rules to the rule function <code>f</code> of a module below, last but before its final
      catch-all case, or before its rule <code>r</code>; or cases to its helper <code>f</code>.
    </dd>
  </dl>
  <p>
    Kanon generates the type <code>t</code> of terms, in OCaml hash-consed records
    <code>{"{ kind; ty; tag }"}</code> (whose table is not safe to use from several OCaml 5
    domains at once, a known limitation). Their <code>kind</code> has the leaves, in the order of
    their declarations, then, for each arity of operators, <code>Op1 of op1 * t</code>,
    <code>Op2 of op2 * t * t</code>, …, and <code>OpN of opn * t list</code>, where the type
    <code>opk</code> has the operators of that arity, with their other arguments
    (<code>Add of checked</code>). <code>ty</code> has the sorts. Rules do not name
    <code>Op2</code>: they write <code>And (a, b)</code>, or <code>a &amp;&amp; b</code>.
  </p>
  <p>
    <code>use</code>, <code>type</code>, <code>sort</code>, <code>of</code>, <code>node</code>,
    <code>infix</code>, <code>prefix</code>, <code>constant</code>, <code>prim</code>,
    <code>oracle</code>, <code>fn</code>, <code>rule</code>, <code>extend</code> and
    <code>before</code> are keywords, with those of OCaml that Kanon uses (<code>let</code>,
    <code>match</code>, <code>if</code>, <code>when</code>, <code>as</code>, <code>not</code>,
    …).
  </p>

  <Heading level={2} id="attributes">Attributes</Heading>
  <p>
    Attributes follow what they apply to. Their arguments are names (of functions, nodes and
    constants), integers, <code>true</code> and <code>false</code>, or strings for anything else
    (<code>[@fold f_add]</code>, <code>[@unit 0]</code>, <code>[@ocaml "Bv.t"]</code>). Below,
    <code>v</code> is the type of the values of <code>[@literal v]</code> literals.
  </p>

  <Heading level={3} id="on-types">On types</Heading>
  <table>
    <thead><tr><th>Attribute</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>[@ocaml "M.a"]</code></td>
        <td>
          The OCaml type of an abstract type, which <code>ocaml-types</code> needs.
        </td>
      </tr>
      <tr>
        <td><code>[@lean "A"]</code></td>
        <td>
          The Lean type, if it is not the Kanon name, CamelCased (<code>ext_ty</code> is
          <code>ExtTy</code>). An abstract type is defined by hand in Lean, unless
          <code>[@lean]</code> names an existing type.
        </td>
      </tr>
      <tr>
        <td><code>[@noeq]</code></td>
        <td>
          On an abstract type: <code>=</code> and <code>&lt;&gt;</code> are not allowed at this type
          (nor at tuples, options and lists of it).
        </td>
      </tr>
      <tr>
        <td><code>[@equal "M.equal"]</code></td>
        <td>
          On an abstract type <code>a</code>: the OCaml function <code>M.equal : a -> a -> bool</code>
          that decides <code>=</code> at this type, rather than <code>Stdlib.( = )</code>. Terms are
          always compared as hash-consed terms, by their tags, never with
          <code>Stdlib.( = )</code>.
        </td>
      </tr>
      <tr>
        <td><code>[@hash "M.hash"]</code></td>
        <td>
          On an abstract type <code>a</code>: the OCaml function <code>M.hash : a -> int</code>
          that hashes its values for hash-consing, rather than <code>Hashtbl.hash</code>.
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={3} id="on-nodes">On nodes and sorts</Heading>
  <p>These go on <code>node</code> and <code>sort</code> declarations, after their typing.</p>
  <table>
    <thead><tr><th>Attribute</th><th>On</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>[@literal bool]</code></td>
        <td>a node of one <code>bool</code></td>
        <td>
          The boolean literals: in patterns, <code>true</code> and <code>false</code> match them;
          the laws build them.
        </td>
      </tr>
      <tr>
        <td><code>[@literal int]</code></td>
        <td>a node of one <code>int</code></td>
        <td>
          The integer literals: in patterns, <code>0</code>, <code>1</code>, … match them,
          <code>#_</code> any of them, and <code>#x</code> binds their value to <code>x</code>;
          the laws build them.
        </td>
      </tr>
      <tr>
        <td><code>[@literal v]</code></td>
        <td>a node of one <code>int</code></td>
        <td>
          Integer literals whose values have the abstract type <code>v</code> (e.g. bit-vectors),
          which <code>#x</code> binds in rules (and their integer in helpers).
        </td>
      </tr>
      <tr>
        <td><code>[@to_term f]</code></td>
        <td>a <code>[@literal v]</code> node</td>
        <td><code>f : v -> t</code> makes the literal of a value, where a value is used as a term.</td>
      </tr>
      <tr>
        <td><code>[@of_term p]</code></td>
        <td>a <code>[@literal v]</code> node</td>
        <td>The primitive <code>p : t -> v</code> reads the value of a literal.</td>
      </tr>
      <tr>
        <td><code>[@raw f p]</code></td>
        <td>a <code>[@literal v]</code> node, any number of times</td>
        <td>
          For <code>f : a1 -> … -> v -> r</code>, the primitive
          <code>p : a1 -> … -> t -> r</code> computes <code>f</code> directly on the literal,
          without reading its value.
        </td>
      </tr>
      <tr>
        <td><code>[@get f]</code></td>
        <td>a sort of one argument</td>
        <td>
          The helper <code>f : t -> int</code> reads that argument from the sort of a term
          (<code>sort TArray of nat [@get length]</code>): Kanon calls <code>f v</code> rather than
          matching the sort of <code>v</code>.
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={3} id="laws">Laws</Heading>
  <p>
    On an operator, the laws derive the first rules of its <em>rule function</em> (the one whose
    spec is the operator over the function's parameters), in this order, before the rules written
    by hand. They are ordinary rules, generated and proved like the others. Here on
    <code>Plus</code>, <code>And</code> and <code>Not</code>, with the rewrites on whole terms (in
    <code>rule not_ : Not v</code>, the case of <code>[@invol]</code> is <code>not x -> x</code>, on
    the operand <code>v</code>):
  </p>
  <table>
    <thead><tr><th>Law</th><th>Rule</th><th>Rewrite</th></tr></thead>
    <tbody>
      <tr>
        <td><code>[@comm]</code></td>
        <td>none</td>
        <td>
          The operands commute: the rules match them in either order, the generated OCaml orders
          them by hash-consing tag (<code>a &amp;&amp; b</code> and <code>b &amp;&amp; a</code> are
          the same term), and in Lean one statement that the operator commutes proves the arms
          that swap them.
        </td>
      </tr>
      <tr>
        <td><code>[@fold f]</code></td>
        <td><code>lits</code>, <code>lit</code></td>
        <td><code>Int i1 + Int i2 -> Int (f i1 i2)</code>, <code>not (Bool b) -> Bool (f b)</code></td>
      </tr>
      <tr>
        <td><code>[@fold f lift]</code></td>
        <td><code>lits</code>, <code>lit</code></td>
        <td><code>Int i1 + Int i2 -> lift (f i1 i2)</code></td>
      </tr>
      <tr>
        <td><code>[@unit c]</code></td>
        <td><code>unit_zero</code>, <code>unit_true</code></td>
        <td><code>x + 0 -> x</code>, <code>x &amp;&amp; true -> x</code></td>
      </tr>
      <tr>
        <td><code>[@zero c]</code></td>
        <td><code>zero_false</code></td>
        <td><code>x &amp;&amp; false -> false</code></td>
      </tr>
      <tr>
        <td><code>[@idem]</code></td>
        <td><code>same</code></td>
        <td><code>x &amp;&amp; x -> x</code></td>
      </tr>
      <tr>
        <td><code>[@invol]</code></td>
        <td><code>not</code>, after the operator</td>
        <td><code>not (not x) -> x</code></td>
      </tr>
    </tbody>
  </table>
  <ul>
    <li>
      <code>[@comm]</code>, <code>[@unit]</code>, <code>[@zero]</code> and <code>[@idem]</code>
      apply to binary operators, <code>[@invol]</code> to unary ones.
    </li>
    <li>
      <code>[@fold f lift]</code>: <code>f : p1 -> … -> a1 -> a2 -> r</code> takes the last
      parameters of the node that it has room for, then the values of the literal operands; they
      are named after the first letter of their type (<code>i1</code>, <code>i2</code>;
      <code>l</code> and <code>r</code> for <code>[@literal v]</code> values).
      <code>lift : r -> t</code>, a function or a node, makes a term of the result. It is optional:
      by default, it is the literal node of the type of the result (the
      <code>[@literal bool]</code> node for <code>bool</code>, the <code>[@literal int]</code> one
      for <code>int</code>, else the leaf of one argument of that type), and nothing for
      <code>v</code>, whose values are terms by <code>[@to_term]</code>. A node is built at the
      sort that its typing gives, or else at the sort of the spec.
    </li>
    <li>
      <code>[@unit c]</code> and <code>[@zero c]</code> take a literal, <code>0</code>,
      <code>1</code>, <code>true</code> or <code>false</code>, which the rule matches, or a
      named constant, which it compares, with <code>=</code>, to the constant at the sort of the
      other operand. The rule is named <code>unit_c</code> or <code>zero_c</code>, after the
      literal (<code>unit_zero</code>, <code>unit_one</code>, <code>zero_false</code>, …) or the
      constant. On an operator that does not commute, <code>c</code> is on the right; on one that
      does, on either side. The term of <code>c</code> is its <code>constant</code>, or else the
      literal node.
    </li>
  </ul>
  <p>With all-ones, the bitwise and of bit-vectors has a named unit:</p>
  <Code
    code={`constant ones (v) = lit_ones (size v)
constant 0 (v) = lit_zero (size v)

node BvAnd : TBitVector n -> TBitVector n -> TBitVector n [@comm] [@unit ones] [@zero 0]`}
  />
  <p>
    Its rule <code>unit_ones</code> returns <code>x</code> from <code>x, y</code>, in either
    order, when <code>y = lit_ones (size x)</code>: the constant <code>ones</code> at the sort of
    <code>x</code>.
  </p>

  <Heading level={3} id="on-functions">On functions, rules and patterns</Heading>
  <table>
    <thead><tr><th>Attribute</th><th>On</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>[@ty_only]</code></td>
        <td>a helper of one term, before its <code>=</code></td>
        <td>
          The helper only reads the sort of the term (<code
            >fn size (v : t) : int [@ty_only] = width (type_of v)</code
          >), so that it may be applied to the operands of a commutative spec, as
          <code>type_of</code>.
        </td>
      </tr>
      <tr>
        <td><code>[@untyped]</code></td>
        <td>a rule function, after its spec</td>
        <td>
          The function also simplifies ill-typed specs: it does not assert the sorts of its
          operands, and the proofs do not assume them.
        </td>
      </tr>
      <tr>
        <td><code>[@comm]</code></td>
        <td>a pattern of a pair</td>
        <td>
          The pattern also matches the components of the pair swapped: <code>(1, ~v) [@comm]</code>
          matches both <code>1, ~v</code> and <code>~v, 1</code>.
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={3} id="floating">Floating attributes</Heading>
  <p>In <code>.knl</code> files, on their own.</p>
  <table>
    <thead><tr><th>Attribute</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>[@@@ocaml_prims "M"]</code></td>
        <td>
          The OCaml module of the primitives, which the generated rules call
          (<code>M.f</code>) and check against their declared types. Required when the language
          has primitives.
        </td>
      </tr>
      <tr>
        <td><code>[@@@ocaml_types "M"]</code></td>
        <td>
          The OCaml module of the types (the output of <code>ocaml-types</code>), which the
          generated rules open. Without it, they must be included where the types are in scope.
        </td>
      </tr>
      <tr>
        <td><code>[@@@lean_root "R"]</code></td>
        <td>The namespace of the Lean model, and the root of its modules (<code>Kanon</code> by default).</td>
      </tr>
      <tr>
        <td><code>[@@@lean_param "x" "T"]</code></td>
        <td>
          A parameter <code>x : T</code> of the semantics, which the Lean statements quantify over
          (e.g. a semantics of floats).
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={2} id="operators">Operators</Heading>
  <p>
    An operator is a word (a lowercase name, such as <code>urem</code>) or a sequence of the
    symbols <code>! $ % &amp; * + - . / : &lt; = &gt; ? @ ^ | ~</code>, of <code>#</code> after
    the first character, and of non-ASCII characters (<code>≤</code>, <code>⊕</code>). Symbols are
    read as in OCaml, as many as possible: <code>a+-b</code> is the operator <code>+-</code>. The
    reserved <code>=</code>, <code>|</code>, <code>-&gt;</code>, <code>&lt;-</code>,
    <code>:</code>, <code>::</code>, <code>;</code> and <code>.</code> cannot be declared, nor
    <code>&lt;&gt;</code>, which is built in at every type.
  </p>

  <Heading level={3} id="precedence">Precedence</Heading>
  <p>
    The first character of an operator gives its precedence and associativity, as in OCaml. From
    the lowest to the highest:
  </p>
  <table>
    <thead><tr><th>Operators</th><th>Associativity</th></tr></thead>
    <tbody>
      <tr><td><code>||</code></td><td>right</td></tr>
      <tr><td><code>&amp;&amp;</code></td><td>right</td></tr>
      <tr>
        <td>
          <code>=…</code> <code>&lt;…</code> <code>&gt;…</code> <code>|…</code> <code>&amp;…</code>
          <code>$…</code> <code>!=</code>, words, and those that start with a non-ASCII character
        </td>
        <td>left</td>
      </tr>
      <tr><td><code>@…</code> <code>^…</code></td><td>right</td></tr>
      <tr><td><code>::</code></td><td>right</td></tr>
      <tr><td><code>+…</code> <code>-…</code></td><td>left</td></tr>
      <tr><td><code>*…</code> <code>/…</code> <code>%…</code></td><td>left</td></tr>
      <tr><td><code>**…</code></td><td>right</td></tr>
      <tr><td>prefix <code>-</code></td><td></td></tr>
      <tr><td>prefix <code>!…</code> <code>~…</code> <code>?…</code></td><td></td></tr>
    </tbody>
  </table>
  <p>
    The prefix operators are <code>-</code>, <code>not</code> (an application, as in OCaml) and
    the symbols that start with <code>!</code>, <code>~</code> or <code>?</code>; the others are
    infix.
  </p>

  <Heading level={3} id="declaring">Declaring an operator</Heading>
  <Code
    code={`infix "&&" = And, b_and
infix "+" = Add, bv_add unchecked, lit_add
infix "urem" = Rem false, bv_rem false, lit_urem
prefix "not" = Not, b_not`}
  />
  <p>
    <code>infix "op" = Node, f args, g</code> declares what <code>a op b</code> builds and matches:
    in expressions, it calls the smart constructor <code>f</code> with the leading arguments
    <code>args</code> (<code>bv_add unchecked a b</code>); in patterns, it matches the node
    (<code>Add (_, a, b)</code>, whatever its parameters); on the values of
    <code>[@literal v]</code> literals, it is the primitive <code>g</code>, which is optional.
    <code>prefix</code> is the same for one operand.
  </p>
  <ul>
    <li>
      The node may fix its parameters, as in <code>Rem false</code>: its patterns then match only
      these (<code>a urem b</code> is <code>Rem (false, a, b)</code>).
    </li>
    <li>
      A word is an infix operator, and no longer a name, from its declaration on: in the rest of
      its file, and in the files read after it (the declarations of a module come before its
      rules, and before the modules it uses after them).
    </li>
    <li>
      Built in: on integers, <code>+</code>, <code>-</code>, <code>*</code>, the prefix
      <code>-</code>, <code>&lt;</code>, <code>&lt;=</code>, <code>&gt;</code> and
      <code>&gt;=</code>; on booleans, <code>&amp;&amp;</code>, <code>||</code> and
      <code>not</code>; at every type (but those of <code>[@noeq]</code>), <code>=</code> and
      <code>&lt;&gt;</code>. On terms, <code>=</code> is the equality of hash-consed terms. Any
      other operator must be declared.
    </li>
  </ul>
</DocPage>

<style>
  .lede {
    font-size: 1.1em;
    color: var(--color2);
  }
  dt {
    margin-top: var(--sp-4);
    font-weight: 600;
  }
  dd {
    margin-left: var(--md-indent);
  }
</style>
