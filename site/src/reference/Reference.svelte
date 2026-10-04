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
    <code>sort</code>, <code>subsort</code>, <code>node</code>, <code>notation</code>,
    <code>infix</code>, <code>prefix</code> and <code>constant</code> items and floating attributes; its rules are in
    <code>.kn</code> files, with <code>prim</code>, <code>oracle</code>, <code>fn</code>,
    <code>rule</code> and <code>extend</code> items. A module <code>path</code> is the pair
    <code>path.knl</code> and <code>path.kn</code>, either of which may be missing.
  </p>
  <p>
    A documentation comment <code>(** … *)</code> right before a <code>type</code>,
    <code>sort</code>, <code>subsort</code>, <code>node</code>, <code>prim</code>, <code>oracle</code>,
    <code>fn</code> or
    <code>rule</code> documents it: it is copied to the generated OCaml (as <code>(** … *)</code>)
    and Lean (as <code>/-- … -/</code>). A plain comment <code>(* … *)</code> is ignored. A
    documentation comment is also accepted before <code>infix</code>, <code>prefix</code> and
    <code>constant</code>, but nothing is generated from it there; anywhere else (before a
    <code>notation</code>, a floating attribute, a case, or at the end of a file) it is an error.
  </p>
  <dl>
    <dt><code>{`use "path"{:kanon}`}</code>, <code>{`use builtin "name"{:kanon}`}</code></dt>
    <dd>
      Uses the module <code>path</code>, relative to the directory of the file, or the module
      <code>name</code> built into <code>kanon</code> (<code>{`use builtin "bool"{:kanon}`}</code>).
      A module is read once; the declarations of a file come before those of the modules it uses,
      and its rules after theirs.
    </dd>

    <dt><code>type x attrs</code>, <code>type x attrs = | C of a * b | …</code>, <code>type x attrs = {"{ f : a; … }"}</code></dt>
    <dd>
      An abstract, variant or record type, of the arguments of nodes and of the helpers.
      <code>int</code> (arbitrary precision), <code>bool</code>, <code>unit</code>, tuples,
      <code>option</code>, <code>list</code> and <code>array</code> (see <a href="#arrays">Arrays</a>)
      are built in; <code>nat</code>, in the arguments
      of nodes and sorts, is an OCaml <code>int</code> (a width, an index) and a Kanon
      <code>int</code>; it is also accepted in the signatures of functions, rules and primitives, as a
      synonym of <code>int</code> (<code>Z.t</code> in OCaml, not checked to be non-negative).
      <code>t</code>, the type of terms, and <code>ty</code>, the type of their
      sorts, are generated from the nodes and the sorts, and cannot be declared.
    </dd>

    <dt><code>sort S attrs</code>, <code>sort S of a * b attrs</code></dt>
    <dd>A sort, the type of a term: a constructor of <code>ty</code>.</dd>

    <dt><code>{`subsort S of a * b : P x y attrs{:kanon}`}</code></dt>
    <dd>
      A subsort <code>S</code> of the sort <code>P</code>, such as
      <code>{`subsort TNonzero of nat : TBitVector n{:kanon}`}</code>. It has the arguments of its
      parent (the same number, of the same types), which the parent applies, as distinct variables.
      A node may use it in its typing, for an operand or its result
      (<code>{`node Div of bool : TBitVector n -> TNonzero n -> TBitVector n{:kanon}`}</code>): a term
      of a subsort is accepted wherever its parent is expected, and not the reverse. It has no
      constructor of its own and no meaning in OCaml, where the types and rules erase it to its
      parent; it is only trusted, but in <code>ocaml-typed</code>, where the tags of its terms refine
      those of its parent, and in Lean, where <code>{`[@lean "P"]{:kanon}`}</code> gives it a
      predicate. It is not an argument of a sort, nor an annotation <code>(v : S n)</code>, and its
      parent is a sort, not a subsort. Only rules have the assumptions and obligations of their
      subsorts, since functions have no sort annotations; a <code>[@comm]</code> node whose operands
      have different subsorts is rejected.
    </dd>

    <dt><code>node C of a * b (x, y) : s1 -> s2 -> s when e attrs</code></dt>
    <dd>
      A node: a constructor of terms, with its arguments <code>a * b</code> (named <code>x</code>,
      <code>y</code> in its typing), and its typing, all optional. Its operands, then its result,
      have the sorts <code>s1</code>, <code>s2</code>, <code>s</code>, terms of <code>ty</code> over
      the arguments and over variables, which stand for any sort (or any value), under the condition
      <code>e</code> (see <a href="./#typings">Typings</a>). A node without operands
      (<code>{`node Var of var{:kanon}`}</code>) is a leaf; one with <code>k</code> operands is an
      operator of arity <code>k</code>; one whose only operand sort is a list,
      <code>{`node Distinct : a list -> TBool{:kanon}`}</code>, an operator of any number of
      operands, all of the sort <code>a</code>.
    </dd>

    <dt id="notation"><code>{`notation C{:kanon}`}</code></dt>
    <dd>
      Literal patterns for the leaf <code>C</code>, of one <code>bool</code> or <code>int</code>
      argument, a sugar of patterns: <code>true</code> and <code>false</code> stand for
      <code>{`C true{:kanon}`}</code> and <code>{`C false{:kanon}`}</code> (a <code>bool</code>
      notation), the numerals <code>0</code>, <code>1</code>, <code>-1</code>, … for
      <code>{`C 0{:kanon}`}</code>, … (an <code>int</code> one), and <code>#x</code> and
      <code>#_</code> for <code>{`C x{:kanon}`}</code> and <code>{`C _{:kanon}`}</code> (either),
      <code>#x</code> binding the argument. A language may have any number of notations. A literal
      is resolved by its kind (numerals, booleans), then, if several notations remain, by the head
      of the sort of its position (an operand of a spec, an argument of a node in a pattern, a
      parameter of a helper annotated with a sort), compared with the result sort of each notation's
      node; otherwise it is an error, and the pattern names the node
      (<code>{`Int x{:kanon}`}</code>).
    </dd>

    <dt><code>{`infix "op" = Node, f args, g{:kanon}`}</code>, <code>{`prefix "op" = Node, f args, g{:kanon}`}</code></dt>
    <dd>An operator on terms; <code>g</code> is optional (see <a href="#operators">Operators</a>).</dd>

    <dt><code>{`constant c = e{:kanon}`}</code>, <code>{`constant c (v) = e{:kanon}`}</code></dt>
    <dd>
      The term of the constant <code>c</code>, at the sort of the term <code>v</code>, for the laws
      <code>{`[@unit c]{:kanon}`}</code> and <code>{`[@zero c]{:kanon}`}</code>. <code>c</code> is a
      literal (<code>0</code>, <code>1</code>, <code>true</code> or <code>false</code>), whose
      <code>constant</code> is optional: Kanon otherwise builds the node of its notation, at the
      sort of the spec (<code>{`Bool false{:kanon}`}</code>, <code>{`Int 0{:kanon}`}</code>). Or
      <code>c</code> is a name, such as <code>ones</code> for the bit-vector of ones of a width:
      <code>{`constant ones (v) = lit_ones (size v){:kanon}`}</code>.
    </dd>

    <dt><code>{`[@@@name "arg" …]{:kanon}`}</code></dt>
    <dd>A floating attribute (see <a href="#floating">below</a>).</dd>

    <dt><code>{`prim f : a -> b{:kanon}`}</code>, <code>{`oracle f : a -> b{:kanon}`}</code></dt>
    <dd>
      A primitive, implemented by hand in OCaml (in the module of
      <code>{`[@@@ocaml_prims]{:kanon}`}</code>) and in Lean; the generated code checks that both
      define it, at this type. The Lean model takes an oracle as a parameter, so that the proofs may
      not rely on its behaviour (e.g. a hash-consing order). <code>{`[@no_lean]{:kanon}`}</code>
      after the type leaves a primitive out of Lean (see <a href="#on-functions">below</a>).
    </dd>

    <dt><code>fn f (x : a) (y z : b) (v : S args) : c attrs = e</code></dt>
    <dd>
      A helper. All functions can call each other. A parameter of type <code>t</code> may be
      annotated with its sort instead (<code>{`(v : TBitVector n){:kanon}`}</code>): it binds the
      variables of the sort in the body, the generated OCaml asserts it on entry, and literals in
      patterns on <code>v</code> resolve with it. The result may be annotated with a sort too
      (<code>{`fn double (v : TInt) : TInt{:kanon}`}</code>): the generated OCaml asserts it on exit,
      and <code>ocaml-typed</code> gives the function the tags of its sorts. Lean ignores the
      annotation.
    </dd>

    <dt><code>rule f params : spec attrs = | r: p -> e | …</code>, <code>… = e</code>, <code>rule f params : spec attrs</code></dt>
    <dd>
      A rule function: it returns a term that refines the raw term <code>spec</code>. Its cases
      match the operands of the spec and are its rules, named by their labels, tried in order after
      the rules derived from the laws of the spec; it ends with the rule <code>default</code>,
      which builds the spec, unless its last case matches anything. When the spec is a node over
      variables, they are its parameters.
    </dd>

    <dt><code>{`extend rule M.f before r = | r': p -> e | …{:kanon}`}</code>, <code>{`extend fn M.f = | p -> e | …{:kanon}`}</code></dt>
    <dd>
      Adds rules to the rule function <code>M.f</code> of a module below (qualified, as everywhere
      outside its own module: see <a href="#names">Names and modules</a>), last but before its final
      catch-all case (<code>_</code>, or a tuple of blanks such as <code>_, _</code>, which is the same:
      <code>{`x, _{:kanon}`}</code> and <code>{`_ as x{:kanon}`}</code> are not), or before its
      rule <code>r</code>; or cases to its helper <code>f</code>. A case that cannot be added is an
      error.
    </dd>
  </dl>
  <p>
    Kanon generates the type <code>t</code> of terms, in OCaml hash-consed records
    <code>{`{ kind; ty; tag }{:ocaml}`}</code> (whose table is not safe to use from several OCaml 5
    domains at once, a known limitation). Their <code>kind</code> has the leaves, in the order of
    their declarations, then, for each arity of operators, <code>{`Op1 of op1 * t{:ocaml}`}</code>,
    <code>{`Op2 of op2 * t * t{:ocaml}`}</code>, …, and
    <code>{`OpN of opn * t list{:ocaml}`}</code>, where the type <code>opk</code> has the operators
    of that arity, with their other arguments (<code>{`Add of checked{:ocaml}`}</code>).
    <code>ty</code> has the sorts. Rules do not name <code>Op2</code>: they write
    <code>{`And (a, b){:kanon}`}</code>, or <code>{`a && b{:kanon}`}</code>.
  </p>
  <p>
    In expressions, <code>{`(C x : S args){:kanon}`}</code> builds the node
    <code>{`C x{:kanon}`}</code> at the sort <code>{`S args{:kanon}`}</code>, which its typing must
    allow: a leaf whose sort its arguments do not determine
    (<code>{`node BitVec of int : TBitVector n{:kanon}`}</code>) is built this way. The sort may be
    any expression of type <code>ty</code>: <code>{`(Field (i, v) : field_ty v i){:kanon}`}</code>; the typing of an
    operator is then not checked against it.
  </p>
  <p>
    <code>use</code>, <code>builtin</code>, <code>type</code>, <code>sort</code>,
    <code>subsort</code>, <code>notation</code>, <code>of</code>, <code>node</code>, <code>infix</code>,
    <code>prefix</code>, <code>constant</code>, <code>prim</code>, <code>oracle</code>, <code>fn</code>, <code>rule</code>, <code>extend</code>
    and <code>before</code> are keywords, with those of OCaml that Kanon uses (<code>let</code>,
    <code>match</code>, <code>if</code>, <code>when</code>, <code>as</code>, <code>not</code>, …).
  </p>

  <Heading level={3} id="names">Names and modules</Heading>
  <p>
    A module is a file: <code>bitvec.knl</code> and <code>bitvec.kn</code> are the module
    <code>Bitvec</code>, and <code>{`use builtin "bool"{:kanon}`}</code> is <code>Bool</code>. The
    names of the functions, rule functions, primitives and constants are scoped by module, so that
    an <code>Int.add</code> and a <code>Bitvec.add</code> live in the same language. Nodes, sorts,
    subsorts, types, their constructors and fields, and the labels of rules are not: they are those
    of the terms that Kanon generates.
  </p>
  <ul>
    <li>
      In its module, a name is <em>plain</em> (<code>add</code>); from another module it is
      <em>qualified</em>: <code>{`Bitvec.add a b{:kanon}`}</code>, a module and a name with a dot
      and no space. A definition (<code>fn</code>, <code>rule</code>, <code>prim</code>,
      <code>constant</code>) is always plain.
    </li>
    <li>
      A plain name is that of the module of the file where it is written, and never that of a
      module that it uses (there is no implicit opening, so no ambiguity): in a
      <code>extend</code> of another module's function, the cases call their own module's names,
      and <code>Bool.of_bool</code> for the bool module's. A variable may not have the name of a
      function of its module.
    </li>
    <li>
      The names that Kanon provides, <code>type_of</code>, the functions on arrays,
      <code>tag_le</code> and <code>mk_commut_binop</code>, are never qualified, and no module can
      define them.
    </li>
    <li>
      The attributes (<code>{`[@fold Int.add]{:kanon}`}</code>, <code>{`[@get size]{:kanon}`}</code>,
      <code>{`[@unit ones]{:kanon}`}</code>), <code>infix</code>, <code>prefix</code> and
      <code>extend</code> name functions and constants in the same way. A literal constant belongs
      to its module (<code>Bitvec.0</code>).
    </li>
    <li>
      The backends nest the names the same way: Lean defines <code>Bitvec.add</code> in the
      namespace <code>Bitvec</code>, the typed interface has a module <code>Bitvec</code>, and the
      OCaml rules module has the same modules, <code>Rules.Bitvec.add</code>. Primitives keep their plain
      name in the module of the primitives.
    </li>
  </ul>

  <Heading level={3} id="arrays">Arrays</Heading>
  <p>
    <code>t array</code> is the type of immutable arrays of <code>t</code>: a type of its own, not a
    list under other names (<code>Iarray.t</code> in OCaml, <code>Array t</code> in Lean). It has
    a literal and five functions, which are built in: their names cannot be declared again.
  </p>
  <table>
    <thead><tr><th>Expression</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>{`[| a; b |]{:kanon}`}</code>, <code>{`[||]{:kanon}`}</code></td>
        <td>The array of these elements. <code>{`[||]{:kanon}`}</code> needs its type to be known (a result, an argument).</td>
      </tr>
      <tr><td><code>{`array_length a{:kanon}`}</code></td><td>The number of elements, an <code>int</code>.</td></tr>
      <tr><td><code>{`array_get a i{:kanon}`}</code></td><td>The element at the index <code>i</code>, which must be in bounds.</td></tr>
      <tr>
        <td><code>{`array_set a i x{:kanon}`}</code></td>
        <td>A copy of <code>a</code> where the element at <code>i</code>, in bounds, is <code>x</code>; <code>a</code> is not changed.</td>
      </tr>
      <tr>
        <td><code>{`array_of_list l{:kanon}`}</code>, <code>{`array_to_list a{:kanon}`}</code></td>
        <td>The conversions between lists and arrays.</td>
      </tr>
      <tr>
        <td><code>{`a = b{:kanon}`}</code>, <code>{`a <> b{:kanon}`}</code></td>
        <td>
          Structural equality: the same length and equal elements. A node with an array argument is
          hash-consed on it.
        </td>
      </tr>
    </tbody>
  </table>
  <p>
    There is no cons, concatenation, array pattern or <code>a.(i)</code>: an array is read and updated by
    index, and a recursion is written on its list (<code>array_to_list</code>). An index out of
    bounds is a precondition that Kanon does not check: OCaml raises <code>Invalid_argument</code>,
    and Lean's total operations (<code>arrayGet</code> and <code>arraySet</code>, in
    <code>KanonCore.Array</code>, with their lemmas) return <code>default</code> and the array
    itself, which must not be relied on, so a rule tests the index first
    (<code>{`Vec a, #k when 0 <= k && k < array_length a -> …{:kanon}`}</code>). The generated OCaml
    uses the standard <code>Iarray</code> (OCaml 5.4) and needs nothing else.
  </p>

  <Heading level={2} id="attributes">Attributes</Heading>
  <p>
    Attributes follow what they apply to. Their arguments are names (of functions, nodes and
    constants), integers, <code>true</code> and <code>false</code>, or strings for anything else
    (<code>{`[@fold f_add]{:kanon}`}</code>, <code>{`[@unit 0]{:kanon}`}</code>,
    <code>{`[@ocaml "Bv.t"]{:kanon}`}</code>).
  </p>

  <Heading level={3} id="on-types">On types</Heading>
  <table>
    <thead><tr><th>Attribute</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>{`[@ocaml "M.a"]{:kanon}`}</code></td>
        <td>
          The OCaml type of an abstract type, which <code>ocaml-types</code> needs. Optional on a
          record or a variant: <code>ocaml-types</code> then re-exports that type
          (<code>{`type checked = M.checked = { … }{:ocaml}`}</code>), which OCaml checks against
          the declaration, rather than generating it.
        </td>
      </tr>
      <tr>
        <td><code>{`[@lean "A"]{:kanon}`}</code></td>
        <td>
          The Lean type, if it is not the Kanon name, CamelCased (<code>ext_ty</code> is
          <code>ExtTy</code>). An abstract type is defined by hand in Lean, unless
          <code>{`[@lean]{:kanon}`}</code> names an existing type.
        </td>
      </tr>
      <tr>
        <td><code>{`[@noeq]{:kanon}`}</code></td>
        <td>
          On an abstract type: <code>=</code> and <code>&lt;&gt;</code> are not allowed at this type
          (nor at tuples, options and lists of it).
        </td>
      </tr>
      <tr>
        <td><code>{`[@equal "M.equal"]{:kanon}`}</code></td>
        <td>
          On an abstract type <code>a</code>: the OCaml function
          <code>{`M.equal : a -> a -> bool{:ocaml}`}</code> that decides <code>=</code> at this
          type, rather than <code>{`Stdlib.( = ){:ocaml}`}</code>. Terms are always compared as
          hash-consed terms, by their tags, never with <code>{`Stdlib.( = ){:ocaml}`}</code>.
        </td>
      </tr>
      <tr>
        <td><code>{`[@hash "M.hash"]{:kanon}`}</code></td>
        <td>
          On an abstract type <code>a</code>: the OCaml function
          <code>{`M.hash : a -> int{:ocaml}`}</code> that hashes its values for hash-consing, rather
          than <code>{`Hashtbl.hash{:ocaml}`}</code>.
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={3} id="on-sorts">On sorts and subsorts</Heading>
  <table>
    <thead><tr><th>Attribute</th><th>On</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>{`[@get f]{:kanon}`}</code></td>
        <td>a sort of one argument</td>
        <td>
          The helper <code>{`f : t -> int{:kanon}`}</code> reads that argument from the sort of a
          term (<code>{`sort TArray of nat [@get length]{:kanon}`}</code>): Kanon calls
          <code>{`f v{:kanon}`}</code> rather than matching the sort of <code>v</code>.
        </td>
      </tr>
      <tr>
        <td><code>{`[@lean "P"]{:kanon}`}</code></td>
        <td>a subsort</td>
        <td>
          The Lean predicate <code>{`P : Term → Prop{:lean}`}</code> that its terms satisfy, written
          by hand in the semantics. The Lean statements of a rule function assume it of an operand
          at a position of the subsort (<code>{`Nonzero v →{:lean}`}</code>), and the function must
          prove that what it returns, when its node has the subsort for its result, satisfies it
          (<code>f.post.main.Stmt</code>, proved by hand with <code>{`@[kanon_arm]{:lean}`}</code>).
          Without it, Lean ignores the subsort.
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={3} id="laws">Laws</Heading>
  <p>
    On an operator, the laws derive the first rules of its <em>rule function</em> (the one whose
    spec is the operator over the function's parameters), in this order, before the rules written by
    hand. They are ordinary rules, generated and proved like the others. Here on <code>Plus</code>,
    <code>And</code> and <code>Not</code>, with the rewrites on whole terms (in
    <code>{`rule not_ : Not v{:kanon}`}</code>, the case of <code>{`[@invol]{:kanon}`}</code> is
    <code>{`not x -> x{:kanon}`}</code>, on the operand <code>v</code>):
  </p>
  <table>
    <thead><tr><th>Law</th><th>Rule</th><th>Rewrite</th></tr></thead>
    <tbody>
      <tr>
        <td><code>{`[@comm]{:kanon}`}</code></td>
        <td>none</td>
        <td>
          The operands commute: the rules match them in either order, the generated OCaml orders
          them by hash-consing tag (<code>{`a && b{:kanon}`}</code> and
          <code>{`b && a{:kanon}`}</code> are the same term), and in Lean one statement that the
          operator commutes proves the arms that swap them.
        </td>
      </tr>
      <tr>
        <td><code>{`[@fold f]{:kanon}`}</code></td>
        <td><code>lits</code>, <code>lit</code></td>
        <td><code>{`Int i1 + Int i2 -> Int (f i1 i2){:kanon}`}</code>, <code>{`not (Bool b) -> Bool (f b){:kanon}`}</code></td>
      </tr>
      <tr>
        <td><code>{`[@fold f lift]{:kanon}`}</code></td>
        <td><code>lits</code>, <code>lit</code></td>
        <td><code>{`Int i1 + Int i2 -> lift (f i1 i2){:kanon}`}</code></td>
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
  <ul>
    <li>
      <code>{`[@comm]{:kanon}`}</code>, <code>{`[@unit]{:kanon}`}</code>,
      <code>{`[@zero]{:kanon}`}</code> and <code>{`[@idem]{:kanon}`}</code> apply to binary
      operators, <code>{`[@invol]{:kanon}`}</code> to unary ones.
    </li>
    <li>
      <code>{`[@fold f lift]{:kanon}`}</code>: <code>f : p1 -> … -> a1 -> a2 -> r</code> takes the
      last parameters of the node that it has room for, then the values of the literal operands (the
      arguments of their notations). Its parameters of type <code>ty</code> right before the values
      receive the sorts of the literal operands, in order
      (<code>{`fn z_add (s _ : ty) (l r : int) : int{:kanon}`}</code>).
      <code>{`lift : r -> t{:kanon}`}</code>, a
      function or a node, makes a term of the result. It is optional: by default, it is the node
      of the notation of the type of the result (<code>bool</code> or <code>int</code>), else the
      leaf of one argument of that type. A node is built at the sort that its typing gives, or
      else at the sort of the spec.
    </li>
    <li>
      <code>{`[@unit c]{:kanon}`}</code> and <code>{`[@zero c]{:kanon}`}</code> take a literal,
      <code>0</code>, <code>1</code>, <code>true</code> or <code>false</code>, which the rule
      matches, or a named constant, which it compares, with <code>=</code>, to the constant at the
      sort of the other operand. The rule is named <code>unit_c</code> or <code>zero_c</code>, after
      the literal (<code>unit_zero</code>, <code>unit_one</code>, <code>zero_false</code>, …) or the
      constant. On an operator that does not commute, <code>c</code> is on the right; on one that
      does, on either side. A literal is resolved as in patterns, at the sort of the operands, and
      its term is its <code>constant</code>, or else the node of its notation.
    </li>
  </ul>
  <p>With all-ones, the bitwise and of bit-vectors has a named unit:</p>
  <Code
    code={`constant ones (v) = lit_ones (size v)
constant 0 (v) = lit_zero (size v)

node BvAnd : TBitVector n -> TBitVector n -> TBitVector n [@comm] [@unit ones] [@zero 0]`}
  />
  <p>
    Its rule <code>unit_ones</code> returns <code>x</code> from <code>{`x, y{:kanon}`}</code>, in
    either order, when <code>{`y = lit_ones (size x){:kanon}`}</code>: the constant
    <code>ones</code> at the sort of <code>x</code>.
  </p>

  <Heading level={3} id="on-functions">On functions, rules and patterns</Heading>
  <table>
    <thead><tr><th>Attribute</th><th>On</th><th>Meaning</th></tr></thead>
    <tbody>
      <tr>
        <td><code>{`[@ty_only]{:kanon}`}</code></td>
        <td>a helper of one term (<code>fn</code>), before its <code>=</code></td>
        <td>
          The helper only reads the sort of the term (<code
            >fn size (v : t) : int [@ty_only] = width (type_of v)</code
          >), so that it may be applied to the operands of a commutative spec, as
          <code>type_of</code>.
        </td>
      </tr>
      <tr>
        <td><code>{`[@no_lean]{:kanon}`}</code></td>
        <td>a <code>fn</code>, after its result type; a <code>prim</code>, after its type</td>
        <td>
          Generated in OCaml (by every OCaml backend), and left out of every Lean file. A function
          that is modelled in Lean (any other helper or rule function, or the typing of a node) may
          not call it; a <code>{`[@no_lean]{:kanon}`}</code> helper may call anything, and the cases
          that <code>extend fn</code> adds to it are not modelled either. It cannot mark a rule
          function, an oracle, a sort, a node or a type, which are proved or modelled.
          <code>{`[@ty_only]{:kanon}`}</code> combines with it.
        </td>
      </tr>
      <tr>
        <td><code>{`[@total]{:kanon}`}</code></td>
        <td>a <code>fn</code>, after its result type</td>
        <td>
          A per-node function: its body ends with a match on its first term parameter, which must
          have a case for every node of the language (leaf or operator). A catch-all case (<code
            >_</code
          >, a variable, even guarded) is an error, and so is a missing node, listed with all the
          others. The check runs on the final language, after the cases of every <code
            >extend fn</code
          > are added (which append their cases): a module that adds nodes extends the function. A
          case covers a node if it has no guard, and its patterns on the node's arguments and on the
          other scrutinees match anything (<code>Int _</code> does, <code>Int 0</code> does not).
          Combines with <code>{`[@no_lean]{:kanon}`}</code>.
        </td>
      </tr>
      <tr>
        <td><code>{`[@untyped]{:kanon}`}</code></td>
        <td>a rule function, after its spec</td>
        <td>
          The function also simplifies ill-typed specs: it does not assert the sorts of its
          operands, and the proofs do not assume them.
        </td>
      </tr>
      <tr>
        <td><code>{`[@comm]{:kanon}`}</code></td>
        <td>a pattern of a pair</td>
        <td>
          The pattern also matches the components of the pair swapped:
          <code>{`(1, ~v) [@comm]{:kanon}`}</code> matches both <code>{`1, ~v{:kanon}`}</code> and
          <code>{`~v, 1{:kanon}`}</code>.
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
        <td><code>{`[@@@ocaml_prims "M"]{:kanon}`}</code></td>
        <td>
          The OCaml module of the primitives, which the generated rules call
          (<code>M.f</code>) and check against their declared types. Required when the language
          has primitives.
        </td>
      </tr>
      <tr>
        <td><code>{`[@@@ocaml_types "M"]{:kanon}`}</code></td>
        <td>
          The OCaml module of the types (the output of <code>ocaml-types</code>), which the
          generated rules open. Without it, they must be included where the types are in scope.
        </td>
      </tr>
      <tr>
        <td><code>{`[@@@ocaml_rules "M"]{:kanon}`}</code></td>
        <td>
          The OCaml module of the rules (the output of <code>ocaml</code>), which the
          implementation of <code>ocaml-typed</code> includes. Required by
          <code>ocaml-typed</code>.
        </td>
      </tr>
      <tr>
        <td><code>{`[@@@traversals]{:kanon}`}</code></td>
        <td>
          <code>ocaml</code> also generates the <a href="#traversals">traversals</a> of the terms and
          of the sorts.
        </td>
      </tr>
      <tr>
        <td><code>{`[@@@lean_root "R"]{:kanon}`}</code></td>
        <td>The namespace of the Lean model, and the root of its modules (<code>Kanon</code> by default).</td>
      </tr>
      <tr>
        <td><code>{`[@@@lean_param "x" "T"]{:kanon}`}</code></td>
        <td>
          A parameter <code>{`x : T{:lean}`}</code> of the semantics, which the Lean statements
          quantify over (e.g. a semantics of floats).
        </td>
      </tr>
    </tbody>
  </table>

  <Heading level={3} id="traversals">Traversals</Heading>
  <p>
    With <code>{`[@@@traversals]{:kanon}`}</code>, <code>kanon ocaml</code> generates, after the
    rules, <code>map_children</code>, <code>iter_children</code>, <code>exists_child</code> and
    <code>for_all_child</code> over the terms, and <code>map_ty_children</code>,
    <code>iter_ty_children</code>, <code>exists_ty_child</code> and <code>for_all_ty_child</code>
    over the sorts: a case per node (or sort constructor) in the order of its arguments, with no
    intermediate list, and the cases of the nodes of every module.
  </p>
  <ul>
    <li>
      The children of a node are the values of type <code>t</code> in its arguments and operands:
      directly, in a <code>t list</code>, <code>t array</code> or <code>t option</code>, in a tuple,
      or in a type of the language that mentions <code>t</code>, a record or a variant
      (<code>{`type block = { owner : var; offset : t; size : t }{:kanon}`}</code>), whose own
      traversal is generated. An abstract type is opaque. The children of a sort are its
      <code>ty</code> arguments, in the same shapes.
    </li>
    <li>
      <code>map_children f v</code> rebuilds <code>v</code> from its mapped children, in order:
      through the smart constructor of the node if a rule function has it as its spec, else the raw
      node at the sort that its typing gives (a leaf may declare a computed sort,
      <code>{`node Tuple of t list (vs) : TTuple (types_of vs){:kanon}`}</code>), or at the sort of
      <code>v</code> if it has no typing.
    </li>
    <li>
      <code>exists_child</code> stops at the first child that satisfies its predicate, and composes
      with the recursion of the host without a handler:
      <code>{`let rec has_var v = is_var v || exists_child has_var v{:ocaml}`}</code>. Variables and
      binders are the host's: Kanon does not know them. Nothing is generated for Lean.
    </li>
  </ul>

  <Heading level={2} id="backends">Backends</Heading>
  <p>
    <code>kanon BACKEND FILE...</code> reads the language that the files declare, usually its one
    <code>.knl</code> file, and writes the generated code on standard output.
  </p>
  <table>
    <thead><tr><th>Backend</th><th>Writes</th></tr></thead>
    <tbody>
      <tr><td><code>ocaml-types</code></td><td>The OCaml types of the language and its hash-consed terms.</td></tr>
      <tr>
        <td><code>ocaml</code></td>
        <td>
          The OCaml rule functions and helpers, then the destructors and tests of the nodes and the
          sorts. For a node <code>BvAdd</code>, <code>as_bvadd</code> returns its arguments in an
          option (the parameters, then the operands) and <code>is_bvadd</code> tests it; for a sort
          <code>TInt</code>, <code>as_tint</code> returns the arguments of the sort and
          <code>is_tint</code> tests it. Their names are <code>as_</code> and <code>is_</code>
          followed by the name of the constructor in lowercase, with no other change, in the module of the file
          that declares the node or the sort: a function of that module cannot have such a name.
        </td>
      </tr>
      <tr>
        <td><code>ocaml-typed</code></td>
        <td>
          The typed interface of the smart constructors, where a term <code>'a t</code> has a
          phantom parameter, a tag, that says what Kanon knows of it: the module
          <code>Tag</code>, with a polymorphic variant type per sort and subsort (they may be
          joined into groups of tags: <code>{`[ Tag.tbitvec | Tag.tfloat ]{:ocaml}`}</code>);
          the signature <code>S</code>, with the types <code>'a t</code> and <code>'a ty</code>,
          the escape hatches <code>untyped</code>, <code>type_</code> and <code>cast</code> (and
          <code>untype_type</code>, <code>type_type</code> on sorts), and a module per Kanon module
          (per file: <code>bitvec.kn</code> and <code>bitvec.knl</code> give <code>Bitvec</code>)
          that has a function for each sort, rule function and destructor declared in it, typed by
          the tags; and <code>Derived</code>, the implementation of <code>S</code>: <code>include</code> of the
          rules (module of <code>{`[@@@ocaml_rules]{:kanon}`}</code>, which has the same modules) with <code>{`type 'a t = raw{:ocaml}`}</code>
          visible, which <code>S</code> hides. A leaf node, which no rule builds, has no function in
          either: a program builds it from the types and gives it its tag with <code>type_</code>. The parameters of a rule function have the types that it declares, as in
          <code>ocaml</code> (a <code>nat</code> is a <code>Z.t</code>).
        </td>
      </tr>
      <tr><td><code>ocaml-tests</code></td><td>OCaml differential tests of the rule functions.</td></tr>
      <tr>
        <td>
          <code>lean-types</code>, <code>lean-syntax</code>, <code>lean-signatures</code>,
          <code>lean-typing</code>, <code>lean-model</code>, <code>lean-statements</code>,
          <code>lean-lifts</code>, <code>lean-soundness</code>
        </td>
        <td>The Lean files of the model and its proofs (see the <a href="proving.html">guide</a>).</td>
      </tr>
      <tr><td><code>lean-all</code></td><td>Each Lean file, as <code>F.lean.gen</code>, in the current directory.</td></tr>
    </tbody>
  </table>

  <Heading level={2} id="bitvectors">Example: bit-vectors</Heading>
  <p>
    The literals of bit-vectors carry their unsigned integer, and their width is in their sort.
    The folds receive the sorts of the literals, and a helper builds a literal at an explicit
    sort:
  </p>
  <Code
    code={`node BitVec of int : TBitVector n
notation BitVec
sort TBitVector of nat [@get size]
node Add of checked : TBitVector n -> TBitVector n -> TBitVector n [@comm] [@fold z_add]
node BitAnd : TBitVector n -> TBitVector n -> TBitVector n [@comm] [@fold z_and] [@zero 0]

infix "+" = Add, add unchecked
infix "land" = BitAnd, and_, z_land

fn z_add (s _ : ty) (l r : int) : int = wrap (size_of_ty s) (l + r)
fn lit (n z : int) : t = (BitVec (wrap n z) : TBitVector n)

rule add : Add (checked, (v1 : TBitVector n), v2) =
  | add_const: Add (c, #k1, r) + #k2 -> add checked (lit n (k1 + k2)) r`}
  />
  <p>
    In <code>add</code>, <code>#k1</code> and <code>#k2</code> are bit-vector literals, which
    bind their integers, and <code>n</code> is the width of the operands, from the annotation of
    the spec.
  </p>

  <Heading level={2} id="operators">Operators</Heading>
  <p>
    An operator is a word (a lowercase name, such as <code>urem</code>) or a sequence of the symbols
    <code>! $ % &amp; * + - . / : &lt; = &gt; ? @ ^ | ~</code>, of <code>#</code> after the first
    character, and of non-ASCII characters (<code>≤</code>, <code>⊕</code>). Symbols are read as in
    OCaml, as many as possible: <code>{`a +- b{:kanon}`}</code> is the operator <code>+-</code>. The
    reserved <code>=</code>, <code>|</code>, <code>-&gt;</code>, <code>&lt;-</code>, <code>:</code>,
    <code>::</code>, <code>;</code> and <code>.</code> cannot be declared, nor
    <code>&lt;&gt;</code>, which is built in at every type.
  </p>
  <p>
    A symbol directly followed by a word is one operator: <code>&lt;u</code>,
    <code>&lt;=s</code> (a lowercase letter, then letters, digits, <code>_</code> and
    <code>'</code>), whatever the declarations: <code>{`a <u b{:kanon}`}</code> is the operator
    <code>&lt;u</code>, whereas <code>{`a < u b{:kanon}`}</code> is <code>&lt;</code> applied to
    <code>{`u b{:kanon}`}</code>. Its precedence is that of its symbol. An operator that the
    language does not declare is an error.
  </p>
  <p>
    Operators are surrounded by spaces: <code>{`x < y{:kanon}`}</code>,
    <code>{`a <u b{:kanon}`}</code>, <code>{`(x + y){:kanon}`}</code>, and not
    <code>{`x<y{:kanon}`}</code>, <code>{`x +y{:kanon}`}</code> or
    <code>{`f x+1{:kanon}`}</code>, which are errors: <code>{`x<y{:kanon}`}</code> is not
    <code>{`x < y{:kanon}`}</code>. A prefix operator is the exception: it is written right before
    its operand, after a space or an opening bracket (<code>{`-x{:kanon}`}</code>,
    <code>{`~(a + b){:kanon}`}</code>, <code>{`x - -y{:kanon}`}</code>); <code>{`- x{:kanon}`}</code>
    and <code>{`a -x{:kanon}`}</code> are errors, and a prefix operator has no word suffix
    (<code>{`-x{:kanon}`}</code> is <code>-</code> and <code>x</code>). The dot, the colon and the
    hash (<code>{`r.f{:kanon}`}</code>, <code>{`(x : t){:kanon}`}</code>,
    <code>{`#x{:kanon}`}</code>) are not operators and need no spaces.
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
          <code>$…</code> <code>!=</code>, and those that start with a non-ASCII character
        </td>
        <td>left</td>
      </tr>
      <tr><td><code>@…</code> <code>^…</code></td><td>right</td></tr>
      <tr><td><code>::</code></td><td>right</td></tr>
      <tr><td><code>+…</code> <code>-…</code></td><td>left</td></tr>
      <tr><td><code>*…</code> <code>/…</code> <code>%…</code>, words</td><td>left</td></tr>
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
    code={`infix "&&" = And, Bool.and_
infix "+" = Add, add unchecked, lit_add
infix "urem" = Rem false, rem false, lit_urem
prefix "not" = Not, Bool.not_`}
  />
  <p>
    <code>{`infix "op" = Node, f args, g{:kanon}`}</code> declares what <code>a op b</code> builds
    and matches: in expressions, it calls the smart constructor <code>f</code> with the leading
    arguments <code>args</code> (<code>{`add unchecked a b{:kanon}`}</code>); in patterns, it
    matches the node (<code>{`Add (_, a, b){:kanon}`}</code>, whatever its parameters); on operands
    that are not terms, it is the function <code>g</code>, which is optional, when they have the
    types of its arguments (<code>{`infix "land" = BitAnd, and_, z_land{:kanon}`}</code> makes
    <code>a land b</code> on integers <code>{`z_land a b{:kanon}`}</code>). <code>prefix</code> is
    the same for one operand.
  </p>
  <ul>
    <li>
      The node may fix its parameters, as in <code>{`Rem false{:kanon}`}</code>: its patterns then
      match only these (<code>a urem b</code> is <code>{`Rem (false, a, b){:kanon}`}</code>).
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
      <code>not</code>; at every type (but those of <code>{`[@noeq]{:kanon}`}</code>),
      <code>=</code> and <code>&lt;&gt;</code>. On terms, <code>=</code> is the equality of
      hash-consed terms. Any other operator must be declared. An operator with a built-in meaning on
      a type cannot have a
      function <code>g</code> on that type.
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
