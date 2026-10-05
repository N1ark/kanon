<script lang="ts">
  // The reference: the declarations, the attributes and the operators of Kanon.
  import { Heading } from "purr";
  import Code from "../components/Code.svelte";
  import DocPage from "../components/DocPage.svelte";

</script>

<DocPage page="reference" headings="h2, h3">
  <h1>Reference</h1>
  <p class="lede">
    The declarations, attributes, operators and rules of Kanon, the code that its backends
    generate, and its language server. The <a href="./">tutorial</a> introduces them on an example,
    and the <a href="proving.html">guide to proofs</a> shows how to prove the generated Lean.
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
    <dt id="use"><code>{`use "path"{:kanon}`}</code>, <code>{`use builtin "name"{:kanon}`}</code></dt>
    <dd>
      Uses the module <code>path</code>, relative to the directory of the file, or the module
      <code>name</code> built into <code>kanon</code> (<code>{`use builtin "bool"{:kanon}`}</code>).
      A module is read once, where it is first used; the declarations of a file come before those of
      the modules it uses, and its rules after theirs. <code>{`use builtin "bool"{:kanon}`}</code>
      reads <code>modules/bool.knl</code> and <code>modules/bool.kn</code> from the binary, as
      <code>bool.knl</code> and <code>bool.kn</code> (in the locations of errors and the headers of
      the generated files); see <a href="#bool-module">The bool module</a>. A language
      <code>lang.knl</code> that starts with <code>{`use builtin "bool"{:kanon}`}</code> and
      <code>{`use "int"{:kanon}`}</code> is made of the bool module and of the module <code>int</code>
      (<code>int.knl</code> and <code>int.kn</code>), and <code>kanon ocaml lang.knl</code>
      generates its rules.
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
      sorts, are generated from the nodes and the sorts, and cannot be declared. A type declared
      <code>nat</code> is used instead of the built-in one. Identifiers may have primes after their
      first character (<code>l'</code>, <code>x''</code>).
    </dd>

    <dt><code>sort S attrs</code>, <code>sort S of a * b attrs</code></dt>
    <dd>
      A sort, the type of a term: a constructor of <code>ty</code>. Sorts and nodes are
      constructors of different types, so their names differ.
    </dd>

    <dt id="subsort"><code>{`subsort S of a * b : P x y attrs{:kanon}`}</code></dt>
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
      operands, all of the sort <code>a</code>. A sort may also be any expression of type
      <code>ty</code> over the arguments and the variables, such as a call of a function, which
      computes the sort of the result from the sorts of the operands and the arguments
      (<code>{`node Field of nat (i) : TTuple tys -> Rules.nth_ty tys i{:kanon}`}</code>); and a leaf
      can declare the computed sort of its result as well,
      <code>{`node Tuple of t list (vs) : TTuple (Rules.types_of vs){:kanon}`}</code>, so that Kanon can
      build it (<code>Tuple vs</code>) and rebuild it. Lean's <code>Typing.lean</code> comes before
      the model, so a function that a typing calls must be a primitive, as for a condition.
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

    <dt id="constant"><code>{`constant c = e{:kanon}`}</code>, <code>{`constant c (v) = e{:kanon}`}</code></dt>
    <dd>
      The term of the constant <code>c</code>, at the sort of the term <code>v</code>, for the laws
      <code>{`[@unit c]{:kanon}`}</code> and <code>{`[@zero c]{:kanon}`}</code>. <code>c</code> is a
      literal (<code>0</code>, <code>1</code>, <code>true</code> or <code>false</code>), whose
      <code>constant</code> is optional: Kanon otherwise builds the node of its notation, at the
      sort of the spec (<code>{`Bool false{:kanon}`}</code>, <code>{`Int 0{:kanon}`}</code>). Or
      <code>c</code> is a name, such as <code>ones</code> for the bit-vector of ones of a width:
      <code>{`constant ones (v) = lit_ones (size v){:kanon}`}</code>. A constant belongs to its module
      like a function: the <code>0</code> of <code>bitvec.knl</code> is <code>Bitvec.0</code>, and
      <code>{`[@unit 0]{:kanon}`}</code> on a node of the module <code>Int</code> does not see it
      (<code>{`[@unit Bitvec.ones]{:kanon}`}</code> names a named constant of another module).
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
      (<code>{`fn wrapping_add (a b : TBitVector n) : TBitVector n = add unchecked a b{:kanon}`}</code>):
      its sort is a sort constructor applied to expressions over the variables that the parameters
      bind (not a subsort), and the function must return a term of that sort. The generated OCaml
      asserts it on exit, as it asserts the sorts of the parameters on entry, and
      <code>ocaml-typed</code> types the function with the tags of its sorts (see
      <a href="#typed">Typed OCaml</a>); Lean does not model the annotation (the model of the
      function is the same, and the proofs assume and prove nothing about its sort). A function whose
      result is not annotated is untyped.
    </dd>

    <dt><code>rule f params : spec attrs = | r: p -> e | …</code>, <code>… = e</code>, <code>rule f params : spec attrs</code></dt>
    <dd>
      A rule function: it returns a term that refines the raw term <code>spec</code>. Its cases
      match the operands of the spec and are its rules, named by their labels, tried in order after
      the rules derived from the laws of the spec; it ends with the rule <code>default</code>,
      which builds the spec, unless its last case matches anything. When the spec is a node over
      variables, <code>C (x1, …, xn)</code>, they are the parameters of the function, at the types
      of the arguments of <code>C</code>; otherwise the function declares its parameters. A rule
      function may instead have an expression as its body, <code>rule f : e = expr</code>, with no
      rules; one without a body only has the rules derived from the laws of its spec, and
      <code>default</code>. See <a href="#rules">Rules</a>.
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
    <code>{`{ kind; ty; tag }{:ocaml}`}</code>. Their <code>kind</code> has the leaves, in the order of
    their declarations, then, for each arity of operators, <code>{`Op1 of op1 * t{:ocaml}`}</code>,
    <code>{`Op2 of op2 * t * t{:ocaml}`}</code>, …, and
    <code>{`OpN of opn * t list{:ocaml}`}</code>, where the type <code>opk</code> has the operators
    of that arity, with their other arguments (<code>{`Add of checked{:ocaml}`}</code>).
    <code>ty</code> has the sorts. Rules do not name <code>Op2</code>: they write
    <code>{`And (a, b){:kanon}`}</code>, or <code>{`a && b{:kanon}`}</code>.
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
    <code>Bitvec</code>, and <code>{`use builtin "bool"{:kanon}`}</code> is <code>Bool</code>: the
    name of a module is that of its file without its extension, capitalised, and must make an OCaml
    module name; two files of the same name, in different directories, are one module. The
    names of the functions, rule functions, primitives and constants are scoped by module, so that
    an <code>Int.add</code> and a <code>Bitvec.add</code> live in the same language. Nodes, sorts,
    subsorts, types, their constructors and fields, and the labels of rules are not: they are those
    of the terms that Kanon generates.
  </p>
  <ul>
    <li>
      In its module, a name is <em>plain</em> (<code>add</code>); from another module it is
      <em>qualified</em>: <code>{`Bitvec.add a b{:kanon}`}</code>, an uppercase name, a dot and a
      lowercase name, with no space (a bare constructor directly followed by <code>.x</code> is read
      as a qualified name). A definition (<code>fn</code>, <code>rule</code>, <code>prim</code>,
      <code>constant</code>) is always plain.
    </li>
    <li>
      A plain name is that of the module of the file where it is written, and never that of a
      module that it uses (there is no implicit opening, so no ambiguity): in a
      <code>extend</code> of another module's function, the cases call their own module's names,
      and <code>Bool.of_bool</code> for the bool module's. The error of an unknown name that another
      module declares says so (<code>unknown function add: Int.add is declared in another module,
      write it qualified</code>). A variable may not have the name of a function of its module, but
      may have that of another module's.
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
    (<code>{`Vec a, #k when 0 <= k && k < array_length a -> …{:kanon}`}</code>); an index is an
    <code>int</code> (<code>Z.t</code> in OCaml: one that does not fit an OCaml <code>int</code>
    raises). The generated OCaml uses the standard <code>Iarray</code> (OCaml 5.4) and needs nothing
    else: <code>ocaml-types</code> generates the equality and the hash of the types that hold an
    array, with <code>Iarray.equal</code> and <code>Iarray.fold_left</code>.
    <a href="https://github.com/N1ark/kanon/tree/main/examples/arrays"><code>examples/arrays</code></a>
    is a small language of integers and arrays of integers (<code>Vec of int array</code>,
    <code>Len</code>, <code>Get</code>, <code>Set</code>): its OCaml is compiled and run by the
    tests, and its Lean model has no proofs, only the generated files.
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
  <p>
    <code>{`[@ty_only]{:kanon}`}</code> on a rule is an error, and so are the other attributes on
    <code>fn</code>, <code>prim</code> and <code>rule</code> (a rule has
    <code>{`[@untyped]{:kanon}`}</code>).
  </p>

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

  <Heading level={2} id="rules">Rules, terms and patterns</Heading>
  <p>
    The bodies of the <code>.kn</code> files: what a rule function may do, how terms are built, and
    what patterns match.
  </p>

  <Heading level={3} id="rule-cases">Rules</Heading>
  <ul>
    <li>The pattern variables of a rule may not shadow the parameters of its function.</li>
    <li>
      A case that an earlier case without a guard already matches can never be taken: Kanon leaves
      it out. It does not look into guards, so a case with a guard, or with a repeated variable or
      an integer literal, which are checks too, covers nothing. The generated OCaml enables the
      warning on unused match cases, which would report any it missed.
    </li>
    <li>
      When the spec of a rule is a commutative node over <code>v1, v2</code> (e.g.
      <code>{`And (v1, v2){:kanon}`}</code>), the cases match them in either order, unless the
      pattern is symmetric (the same once swapped, up to renaming), so
      <code>{`| true_: true, x -> x{:kanon}`}</code> covers both <code>{`true && x{:kanon}`}</code>
      and <code>{`x && true{:kanon}`}</code>. The cases must then name the operands rather than use
      <code>v1</code> and <code>v2</code> (other than as the argument of <code>type_of</code> and
      <code>{`[@ty_only]{:kanon}`}</code> helpers).
    </li>
    <li>
      The cases of a rule whose spec is a binary operator may also be written with the operator: in
      <code>{`rule sub : Sub (checked, v1, v2){:kanon}`}</code>,
      <code>{`| sub_sub: l - (l - r) -> r{:kanon}`}</code> stands for
      <code>{`| sub_sub: l, (l - r) -> r{:kanon}`}</code>.
    </li>
    <li>
      The operands of a spec have the sorts that the typing of its node gives them, which the
      generated OCaml asserts on entry to the rule function (the assertion is compiled out with
      <code>-noassert</code>), and the proofs assume. An operand may be annotated with its sort,
      <code>{`(v : TBitVector n){:kanon}`}</code>, to also assert it and bind its variables in the
      rules: <code>{`rule extract : BvExtract (from_, to_, (v : TBitVector sz)){:kanon}`}</code>
      uses <code>sz</code> for the width of <code>v</code>. A rule that also simplifies ill-typed
      specs is marked <code>{`[@untyped]{:kanon}`}</code> after its spec
      (<code>{`rule eq_untyped : Eq (v1, v2) [@untyped]{:kanon}`}</code>), and asserts nothing.
    </li>
  </ul>

  <Heading level={3} id="terms">Terms</Heading>
  <ul>
    <li>
      Nodes build raw terms, without simplification: <code>{`BvNot v{:kanon}`}</code>,
      <code>{`Add (c, l, r){:kanon}`}</code>. Their sort is inferred from their typing: the sort of
      their result when it only depends on their parameters (<code>TBool</code>), else the sort of
      an operand that has the same sort (<code>type_of v</code> for <code>{`BvNot v{:kanon}`}</code>),
      else the result over the sorts of the operands (<code>{`TBitVector (n + m){:kanon}`}</code> for
      <code>{`BvConcat (l, r){:kanon}`}</code>, from the sorts <code>{`TBitVector n{:kanon}`}</code>
      and <code>{`TBitVector m{:kanon}`}</code> of <code>l</code> and <code>r</code>).
    </li>
    <li>
      <code>type_of v</code> is the sort of the term <code>v</code> (<code>v.ty</code> in OCaml).
    </li>
    <li>
      In rule functions, the operands of commutative operators are put in the hash-consing order:
      <code>{`And (v1, v2){:kanon}`}</code> is the node of <code>mk_commut_binop And v1 v2</code>,
      which puts the operand with the smallest tag on the left. A language with commutative
      operators gets this helper and the oracle <code>tag_le</code> (the hash-consing order,
      compiled to a comparison of the tags in OCaml).
    </li>
    <li>
      <code>{`(C x : S args){:kanon}`}</code> builds the node <code>{`C x{:kanon}`}</code> at the
      sort <code>{`S args{:kanon}`}</code>, which its typing must allow: a leaf whose sort its
      arguments do not determine (<code>{`node BitVec of int : TBitVector n{:kanon}`}</code>) is
      built this way.
    </li>
    <li>
      The sort may also be computed: <code>{`(C x : e){:kanon}`}</code>, for any expression
      <code>e</code> of type <code>ty</code> (a variable, a call of a function or of a primitive, or
      a parenthesised expression such as an <code>if</code> or a <code>match</code>), builds
      <code>{`C x{:kanon}`}</code> at the sort <code>e</code>:
      <code>{`(Tuple vs : TTuple (types_of vs)){:kanon}`}</code> (a sort constructor applied to
      arguments, as above), <code>{`(Var x : s){:kanon}`}</code> for a parameter
      <code>{`s : ty{:kanon}`}</code>, <code>{`(Field (i, v) : field_ty v i){:kanon}`}</code>. A
      computed sort is not checked against the typing of <code>C</code>, which the sort-constructor
      form checks for an operator (a leaf has no operands to check), so it is up to the function to
      build <code>C</code> at a sort that its typing allows. In a rule, the Lean spec of the rule is
      built at the sort of the typing of its node, not at the computed sort, and the
      <code>ocaml-typed</code> backend does not constrain the tag of the result. A constructor-led
      sort is a sort constructor (<code>{`S args{:kanon}`}</code>); <code>{`(C x : t){:kanon}`}</code>
      with the name of a type <code>t</code> is a type annotation. A type annotation
      <code>{`(e : t){:kanon}`}</code> with a parenthesised type or an arrow
      (<code>{`(e : (a * b) list){:kanon}`}</code>) is a syntax error: put the type on a
      <code>let</code>.
    </li>
  </ul>

  <Heading level={3} id="patterns">Patterns</Heading>
  <ul>
    <li>
      Patterns match the kind of a term directly: <code>{`Int z{:kanon}`}</code>,
      <code>{`Add (c, l, r){:kanon}`}</code>. The <a href="#notation">notations</a> of the language
      give literal patterns, which stand for their nodes (<code>true</code>, <code>0</code>,
      <code>#x</code>).
    </li>
    <li>
      A repeated variable matches equal terms (<code>=</code>):
      <code>{`| p, not p -> Bool.v_false{:kanon}`}</code>.
    </li>
    <li>
      The operands of commutative operators match in either order: <code>{`x + #k{:kanon}`}</code>
      also matches <code>{`#k + x{:kanon}`}</code>. The swap is left out when both operands are
      wildcards or variables bound nowhere else, as it matches the same terms.
    </li>
    <li>
      <code>{`p [@comm]{:kanon}`}</code> also matches the components of the pair <code>p</code>
      swapped (the arguments of the rule function): <code>{`(1, ~v) [@comm]{:kanon}`}</code> matches
      both <code>{`1, ~v{:kanon}`}</code> and <code>{`~v, 1{:kanon}`}</code>.
    </li>
    <li>
      Or-patterns, <code>as</code>, <code>when</code> guards, <code>Some</code>/<code>None</code>,
      lists and partial records (<code>{`{ unsigned = true; _ }{:kanon}`}</code>) are supported. Each
      alternative of an or-pattern is tried in turn, together with the guard.
    </li>
  </ul>

  <Heading level={2} id="backends">Backends</Heading>
  <p>
    <code>kanon BACKEND FILE...</code> reads the language that the files declare, usually its one
    <code>.knl</code> file, with the modules it uses (see <a href="#use"><code>use</code></a>), and
    writes the generated code on standard output. <code>kanon --version</code> prints the version of
    Kanon, and <code>kanon lsp</code> runs the <a href="#lsp">language server</a>.
  </p>
  <table>
    <thead><tr><th>Backend</th><th>Writes</th></tr></thead>
    <tbody>
      <tr>
        <td><code>ocaml-types</code></td>
        <td>
          The OCaml types of the language and its hash-consed terms: a standalone OCaml file that
          only needs Zarith (see <a href="#ocaml">OCaml</a>).
        </td>
      </tr>
      <tr>
        <td><code>ocaml</code></td>
        <td>
          The OCaml rule functions and helpers, which need the types in scope, then the destructors
          and tests of the nodes and the sorts (see <a href="#ocaml">OCaml</a>).
        </td>
      </tr>
      <tr>
        <td><code>ocaml-typed</code></td>
        <td>
          The typed interface of the smart constructors, and its implementation from the rules (see
          <a href="#typed">Typed OCaml</a>).
        </td>
      </tr>
      <tr>
        <td><code>ocaml-tests</code></td>
        <td>OCaml differential tests of the rule functions (see <a href="#tests">Tests</a>).</td>
      </tr>
      <tr>
        <td>
          <code>lean-types</code>, <code>lean-syntax</code>, <code>lean-signatures</code>,
          <code>lean-typing</code>, <code>lean-model</code>, <code>lean-statements</code>,
          <code>lean-lifts</code>, <code>lean-soundness</code>
        </td>
        <td>
          The Lean files of the model and its proofs (see <a href="#lean">Lean</a> and the
          <a href="proving.html">guide</a>).
        </td>
      </tr>
      <tr><td><code>lean-all</code></td><td>Each Lean file, as <code>F.lean.gen</code>, in the current directory.</td></tr>
    </tbody>
  </table>
  <p>
    The ppx <code>kanon.ppx_include_file</code> includes the generated OCaml:
    <code>{`[%%include_file "rules.gen.ml"]{:ocaml}`}</code> is the structure of
    <code>rules.gen.ml</code>, a file next to the current one, as
    <code>{`include struct … end{:ocaml}`}</code>, so that it is compiled along with the types it
    needs.
  </p>

  <Heading level={3} id="ocaml">OCaml</Heading>
  <p>
    <code>kanon ocaml-types lang.knl</code> generates the types of the language, in one recursive
    group, with their Kanon names, and its terms:
  </p>
  <Code lang="ocaml" code={`type t = { kind : kind; ty : ty; tag : int }`} />
  <p>
    where <code>kind</code> has the leaves and the <code>Op1</code>, <code>Op2</code>, … of the
    operators, and <code>ty</code> the sorts. <code>node : kind -> ty -> t</code> hash-conses a term:
    a table of ephemerons, keyed on the kind and the sort of the term, gives the term already
    built, or the new one, with the next tag. <code>equal_x</code> and <code>hash_x</code> compare
    and hash the values of each type: structurally, terms by their tags, and the abstract types with
    their <code>{`[@equal]{:kanon}`}</code> and <code>{`[@hash]{:kanon}`}</code>. It only needs
    Zarith (<code>int</code> is <code>Z.t</code>), and the standard <code>Iarray</code> (OCaml 5.4)
    if the language has arrays. The table is not safe to use from several OCaml 5 domains at once: a
    known limitation.
  </p>
  <p>
    <code>kanon ocaml lang.knl</code> generates the rule functions and helpers, which need those
    types in scope: included next to them (<code>{`[%%include_file]{:ocaml}`}</code>), or in the
    module of <code>{`[@@@ocaml_types "Lang_types"]{:kanon}`}</code>, which they open. They call the
    primitives in the module of <code>{`[@@@ocaml_prims "Lang_prims"]{:kanon}`}</code>, which they
    check against the declarations (<code>{`module _ : sig … end = Lang_prims{:ocaml}`}</code>). On
    terms, <code>=</code> compares their tags.
  </p>
  <p>
    The generated module has the structure of the language: a module per Kanon module, that is per
    file (see <a href="#names">Names and modules</a>), with the plain names: the function
    <code>add</code> of <code>bitvec.kn</code> is <code>Bitvec.add</code>, in the output as a
    program, which calls <code>Lang_rules.Bitvec.add</code>. The generated code calls the standard
    library as <code>Stdlib.Int</code>, <code>Stdlib.Bool</code>, …, so a Kanon module named
    <code>Int</code> or <code>Bool</code> does not hide it. A module has:
  </p>
  <ul>
    <li>its functions: every <code>fn</code> and <code>rule</code> (the zero-parameter ones are values, computed once);</li>
    <li>
      the function <code>t_foo</code> of each sort <code>TFoo</code> declared in its files
      (<code>t_bitvec</code>: a <code>nat</code> is an <code>int</code>), which makes the sort from
      its arguments;
    </li>
    <li>the destructors of the nodes and sorts declared in its files (below).</li>
  </ul>
  <p>
    Primitives are not in it: they stay in the module of <code>{`[@@@ocaml_prims]{:kanon}`}</code>,
    under their plain name, whichever module declares them, so two primitives of different modules
    may not have the same name (rename one). The types, <code>node</code>, the terms and the names
    that Kanon provides are not in a module; the destructors are.
  </p>
  <p>
    The functions call each other freely, across modules (an <code>extend</code> calls the functions
    of later modules, and they call back), so they are one recursive group in a module
    <code>Kanon_flat</code>, in the order of their dependencies, under a flat name
    (<code>bitvec_add</code>: the module in lowercase, an underscore, the name; two functions with
    the same flat name are an error); and
    <code>{`module Bitvec = struct let add = Kanon_flat.bitvec_add … end{:ocaml}`}</code> names them.
    A module of <code>Lang_rules</code> is then an alias of the functions of the group: a call of
    <code>Bitvec.add</code> is a direct call of the function, which OCaml inlines when it is small,
    as with flat names. <code>Kanon_flat</code> is not for use, and a module cannot be named
    <code>Kanon_flat</code>.
  </p>
  <p id="destructors">
    <strong>Destructors.</strong> The <code>ocaml</code> backend generates a destructor
    <code>as_foo</code> and a test <code>is_foo</code> for every node and every sort (not the kinds
    that Kanon builds). For the node <code>Foo</code>, <code>as_foo : t -> (args) option</code> gives
    its arguments, as a pattern would bind them: its parameters, then its operands (the list of an
    n-ary node), in a tuple, or alone, or <code>()</code>; <code>is_foo : t -> bool</code> tells
    whether a term is built by <code>Foo</code>. For a sort <code>{`TFoo of nat{:kanon}`}</code>,
    <code>as_tfoo : ty -> int option</code> and <code>is_tfoo</code> read a <code>ty</code>. The name
    is that of the constructor in lowercase (<code>BvAdd</code> gives <code>as_bvadd</code>), in the
    module of the file that declares the node or the sort. A module may not have two items of the
    same name: a function named like a destructor (<code>is_add</code>, in the module of
    <code>Add</code>) or like the function of a sort, or two constructors that differ only by their
    case: these are errors.
  </p>

  <Heading level={3} id="traversals">Traversals</Heading>
  <p>
    A language that has <code>{`[@@@traversals]{:kanon}`}</code> gets, in the output of
    <code>kanon ocaml</code>, functions that traverse its terms and its sorts, one case per node (and
    per sort constructor), in the order of the arguments, with no intermediate list. A node added by
    a later module, or by a later <code>extend</code>, has its case without more: the traversals are
    generated from the final language. They are what a host writes the operations that Kanon does not
    know of (the free variables, a substitution, an evaluation, a search) over: what a variable is,
    or a binder, stays out of Kanon. They are language-wide: top-level functions of the rules module
    (<code>Lang_rules.map_children</code>), in no Kanon module.
  </p>
  <Code
    lang="ocaml"
    code={`val map_children : (t -> t) -> t -> t
val iter_children : (t -> unit) -> t -> unit
val exists_child : (t -> bool) -> t -> bool
val for_all_child : (t -> bool) -> t -> bool
val map_ty_children : (ty -> ty) -> ty -> ty
(* iter_ty_children, exists_ty_child, for_all_ty_child *)`}
  />
  <ul>
    <li>
      The <em>children</em> of a node are the values of type <code>t</code> in its parameters and
      operands, left to right: directly (<code>{`Not of t{:kanon}`}</code>), in a list, an array or an
      option (<code>t list</code>, <code>t array</code>, <code>t option</code>), in a tuple
      (<code>{`(int * t) option{:kanon}`}</code>), and in a type of the language that mentions
      <code>t</code>, a record
      (<code>{`type block = { owner : var; offset : t; size : t }{:kanon}`}</code>, its fields in
      order) or a variant (the arguments of its constructors), possibly recursive, whose traversal is
      generated (<code>kanon__map_block</code>, …). A value of an abstract type is opaque: it has no
      children, even if its OCaml type contains terms. Every other type has none. The sorts have
      children too: the values of type <code>ty</code> in the arguments of the sort constructors
      (<code>{`TSeq of ty`}</code>, <code>{`TTuple of ty list`}</code>), in the same shapes.
    </li>
    <li>
      <code>iter_children f v</code> calls <code>f</code> on the children;
      <code>exists_child f v</code> is true as soon as <code>f</code> is, and does not look at the
      others (<code>for_all_child f v</code> is the dual, <code>false</code> as soon as
      <code>f</code> is). <code>map_children f v</code> rebuilds <code>v</code> from <code>f</code>
      applied to its children, in order: through the <em>smart constructor</em> of the node, if a rule
      function has the node as its spec over its parameters (so that mapping a child to
      <code>0</code> simplifies the sum), else as the raw node, whose sort is that of its typing from
      the new children (the <code>Tuple</code> of <code>{`TTuple (types_of vs){:kanon}`}</code>, see
      <a href="#declarations">node</a>), or, if the node has no typing (a leaf), the sort of
      <code>v</code>. The rebuilt term is always built again (hash-consing finds the existing one). A
      node without children, and a term that is not a node with children, is its own
      <code>map_children</code>.
    </li>
    <li>
      The searches compose with the recursion of the host, with no handler and no allocation:
      <code>{`let rec has_var v = is_var v || exists_child has_var v{:ocaml}`}</code>. A host that wants
      to leave a traversal from inside raises its own exception at the top level
      (<code>iter_children</code> has no handler of its own), and Kanon has no <code>Break</code>: the
      exception of a handler in each call would only stop the innermost loop of a recursive search. On
      a term of 187,000 nodes, the predicate, the iteration with a top-level exception, a built-in
      handler and the list of operands that the traversals replace are within the noise of each other
      (3 to 6 ms), so the choice is that of simplicity.
    </li>
    <li>
      The functions that rebuild the nodes are <code>kanon__rebuild_C</code>,
      <code>{`[@no_lean]{:kanon}`}</code> functions of the rules; the traversals are in OCaml only:
      nothing is generated for Lean, and <code>ocaml-typed</code> does not type them.
      <a href="https://github.com/N1ark/kanon/tree/main/examples/traversals"><code>examples/traversals</code></a>
      is a small language, in two modules, with nodes whose children are in a list, an array, an
      option of a tuple and a record: its OCaml is compiled and run by the tests. It has no Lean files
      (a typing that calls a function is not in Lean's <code>Typing.lean</code>).
    </li>
  </ul>

  <Heading level={3} id="typed">Typed OCaml</Heading>
  <p>
    <code>kanon ocaml-typed lang.knl rules.kn</code> generates the typed interface of the language.
    The terms of the generated OCaml are all of one type, <code>t</code>: nothing stops
    <code>Bitvec.add</code> from being applied to a boolean, but for the assertions on its entry. In
    the typed interface a term is a <code>'a t</code>, where <code>'a</code> is a <em>tag</em>, a
    polymorphic variant that says what Kanon knows of the term, and OCaml rejects the ill-kinded
    calls. The tag is a phantom type: it is only in the type, and a typed term is the same value as
    the untyped one, at no cost. The tags come from the sorts, and the subsorts refine them. For
  </p>
  <Code
    code={`sort TBitVec of nat
subsort TNonzero of nat : TBitVec n
node Add of checked (c) : TBitVec n -> TBitVec n -> TBitVec n
node Div : TBitVec n -> TNonzero n -> TBitVec n`}
  />
  <p>
    the rule functions <code>add</code> and <code>div</code> of <code>Add</code> and
    <code>Div</code>, in a file <code>bitvec.knl</code> and <code>bitvec.kn</code>, give:
  </p>
  <Code
    lang="ocaml"
    code={`module Tag : sig
  type tnonzero = [ \`TNonzero ]
  type tbitvec = [ \`TBitVec | tnonzero ]
end

module type S = sig
  type +'a t
  (* ... *)
  module Bitvec : sig
    val t_bitvec : int -> [> Tag.tbitvec ] ty
    val add : checked -> [< Tag.tbitvec ] t -> [< Tag.tbitvec ] t -> [> Tag.tbitvec ] t
    val div : [< Tag.tbitvec ] t -> [< Tag.tnonzero ] t -> [> Tag.tbitvec ] t
  end
end`}
  />
  <p>What is generated, in the file, for the language (nothing is a functor):</p>
  <ul>
    <li>
      <code>Tag</code> has a tag type per sort and per subsort: the lowercase name of its
      constructor, the variant of that name (<code>{`\`TNonzero`}</code>), and for a sort, the tag
      types of its subsorts too (<code>tbitvec</code>). So an operand
      <code>[&lt; Tag.tbitvec ] t</code> accepts any bit-vector, including a non-zero one
      (<code>[&gt; Tag.tnonzero ] t</code>), and an operand <code>[&lt; Tag.tnonzero ] t</code> only
      one that is known to be non-zero. Two sorts or subsorts that differ by their case have the same
      tag type: an error. The tag types are plain polymorphic variant types, so that a program may
      join them to make groups of tags of its own:
      <code>{`type scalar = [ Tag.tbitvec | Tag.tfloat ]{:ocaml}`}</code>, and
      <code>{`([< scalar ] as 'a) t{:ocaml}`}</code> for a function over them.
    </li>
    <li>
      A term has the tag that its typing gives: a result is <code>[&gt; tag ] t</code> (the result of
      <code>add</code> is a <code>tbitvec</code>, which is not known to be non-zero), and an operand
      <code>[&lt; tag ] t</code>. A subsort is trusted: nothing proves it, and <code>cast</code> gives
      a term the tag that it needs (<code>{`Bitvec.div x (cast y){:ocaml}`}</code>). The width, and
      other values of a sort, are erased: Kanon does not check them. A sort variable
      (<code>Eq</code>, <code>Ite</code>, <code>Distinct</code>) is shared by the operands and the
      result, as <code>'a t</code>. A node without a typing has any tag, <code>_ t</code>.
    </li>
    <li>
      <code>module type S</code>, the signature, with the types of the language and, for
      <code>'a t</code> and the sorts <code>'a ty</code>, the escape hatches:
      <code>untyped : 'a t -> raw</code> forgets the tag (<code>raw</code> is the term <code>t</code>
      of the types of the language), <code>type_ : raw -> 'a t</code> trusts one and
      <code>cast : 'a t -> 'b t</code> changes it, and <code>untype_type</code> and
      <code>type_type</code> do the same for the sorts. They are the identity at run time. Then a
      module per Kanon module, with:
      <ul>
        <li>
          a <code>val t_s</code> per sort (not subsort), which makes the sorts of its terms from its
          arguments, which are those of its constructor (a <code>nat</code> is an <code>int</code>);
        </li>
        <li>
          a <code>val</code> per rule function, named after it, for the node that is its spec. A node
          that no rule function is the spec of, in particular a leaf node (which has no operands to
          build from), has none. The parameters of a rule function have the types that it declares,
          which are those of the generated rules (a <code>nat</code> or an <code>int</code> is a
          <code>Z.t</code>), then come the operands, and the result. Types of the language are those
          of <code>ocaml-types</code>, opened from <code>{`[@@@ocaml_types]{:kanon}`}</code>, or else
          in scope. The docs of the rule function or the node are carried onto the
          <code>val</code>;
        </li>
        <li>
          the destructors of the <code>ocaml</code> backend (see <a href="#destructors">above</a>):
          <code>as_foo : _ t -> (args) option</code>, whose operands are <code>[&gt; tag ] t</code>
          (the tags of the typing of <code>Foo</code>), and <code>is_foo : _ t -> bool</code>, for
          every node, and <code>as_tfoo</code>, <code>is_tfoo</code> for every sort (not subsort), on
          <code>_ ty</code>;
        </li>
        <li>
          a <code>val</code> for a <code>fn</code> whose result is annotated with a sort
          (<code>{`fn wrapping_add (a b : TBitVector n) : TBitVector n{:kanon}`}</code>), in the order
          of its parameters, with the tag of the sort of each annotated parameter
          (<code>[&lt; Tag.tbitvector ] t</code>), any tag for the other terms, the types of the
          others (<code>Z.t</code> for an <code>int</code>), and the tag of its result sort
          (<code>[&gt; Tag.tbitvector ] t</code>):
          <code>val wrapping_add : [&lt; Tag.tbitvector ] t -&gt; [&lt; Tag.tbitvector ] t -&gt; [&gt; Tag.tbitvector ] t</code>,
          implemented by <code>Rules.Bitvec.wrapping_add</code>, of the rules module. So a derived
          helper (<code>wrapping_add</code>, with a rule function <code>add</code> that receives the
          flags) is in the interface with the right tags, defined in Kanon, and the tag of its result
          is trusted, as the subsorts are: the generated rules assert the sort, not the subsort. A
          function without an annotated result has no <code>val</code>.
        </li>
      </ul>
    </li>
    <li>
      A sort that is a parameter (<code>ty</code>) is a <code>raw_ty</code>, since its tag is not
      known, and a term that is a parameter and not an operand (the body of
      <code>{`Exists of (var * ty) list * t{:kanon}`}</code>) is <code>_ t</code>: any tag. A rule
      function has a <code>val</code> whatever its spec. When the spec is a node over the parameters
      of the function, it is typed as the node. Otherwise it is typed by the outermost node of the
      spec: the result has its tag, a parameter that is one of its operands has the tag of that
      operand, and any other parameter has any tag, <code>_ t</code>; a spec that is not a node (a
      call of a function) has any tag everywhere. For instance
      <code>{`rule to_bool (v : t) : Not (Eq (v, zero (size v))){:kanon}`}</code> is
      <code>_ t -> [&gt; tbool ] t</code>.
    </li>
    <li>
      <code>module Derived</code>, the implementation of <code>S</code>: <code>include Lang_rules</code>,
      the module that names <code>{`[@@@ocaml_rules "Lang_rules"]{:kanon}`}</code> (required: the
      output of <code>kanon ocaml</code>), which already has the modules of <code>S</code> with
      their functions, the functions of the sorts and the destructors under the same names, and the
      phantom types and the escape hatches, which are all that <code>Derived</code> adds. In
      <code>Derived</code>, <code>{`type 'a t = raw{:ocaml}`}</code> is visible, so that the rules
      have the types of <code>S</code>; <code>S</code> hides it, since a visible equality would make
      every tag the same type, and OCaml would accept the division by a bit-vector that is not known
      to be non-zero. The generated file checks <code>S</code> against the rules at compile time
      (<code>{`module _ : S = Derived{:ocaml}`}</code>). <code>S</code> is thus a module type that the
      rules module satisfies, once its types are given a phantom parameter; the rules have no tags,
      and what is not in <code>S</code> (the functions that are not rule functions, the prims) is
      simply not exported. There is no functor, so that the escape hatches, which are
      <code>{`let[@inline] f x = x{:ocaml}`}</code>, are known functions to the compiler.
    </li>
  </ul>
  <p>
    The module of a <code>val</code> is that of the Kanon module of its declaration: the file of the
    rule function, the sort or the node, without its extension and with a capital, in
    <code>S</code>, in <code>Derived</code> and in the rules. A module that declares none of them has
    no module in the interface. <code>Tag</code>, <code>S</code>, <code>Derived</code> and
    <code>Kanon_flat</code> are the names of generated modules: a file may not have them. The tags,
    which are not tied to a module, are all in <code>Tag</code>.
  </p>
  <p>
    Leaf nodes have no constructor, in <code>S</code> nor in <code>Derived</code>: no rule builds
    them, and Kanon does not generate one. A program builds them from the types, with the
    hash-consing constructor <code>node</code> at the sort that the typing of the node gives, and
    gives the term its tag with <code>type_</code>. The same goes for the other layers on top of
    <code>Derived</code> (labelled arguments, a nesting of its own, groups of tags):
  </p>
  <Code
    lang="ocaml"
    code={`module Typed = struct
  include (Lang_typed.Derived : Lang_typed.S)

  module Bitvec = struct
    include Bitvec

    let mk_bv v n : [> Lang_typed.Tag.tbitvec ] t =
      type_ (Lang_types.node (BitVec (v, n)) (TBitVec n))
  end
end`}
  />
  <p>
    The constraint <code>(Derived : S)</code> makes the types abstract (<code>type +'a t</code>):
    OCaml checks the rest of the program against the interface <code>S</code>.
  </p>

  <Heading level={3} id="tests">Tests</Heading>
  <p>
    <code>kanon ocaml-tests</code> generates, for every rule function, its spec, a call to it and the
    name of the rule that fires, from random arguments, to be compared by evaluation (Soteria's
    <code>soteria/tests/bv_rules/</code> does so for <code>Bv_values</code>). Every rule function is
    listed with its rules, qualified by its module, including one whose spec annotates the sort of an
    operand (<code>{`(v : TBv sz){:kanon}`}</code>): the generated test checks the sorts first, and
    fails an assertion on operands of the wrong sort, so that the harness draws others (the generator
    itself knows nothing of sorts). A rule function takes terms, so there is no array to draw.
  </p>

  <Heading level={3} id="lean">Lean</Heading>
  <p>
    The Lean files (see <a href="proving.html#files">the files</a> of the guide for what each one
    holds) are generated in the namespace <code>R</code> of
    <code>{`[@@@lean_root "R"]{:kanon}`}</code>. Their conventions:
  </p>
  <ul>
    <li>
      Terms are <code>Term.mk kind ty</code>, with <code>Kind.Var x</code>,
      <code>Kind.Op2 Op2.And a b</code>, <code>Kind.OpN OpN.Distinct l</code>, …; the operators that
      commute are <code>Op2.Comm</code>, from <code>{`[@comm]{:kanon}`}</code>. The typing of the
      operators is <code>Op2.WT op a b t</code>, over the sorts of the operands and of the result,
      and <code>OpN.WT op e t</code>, over the sort <code>e</code> of all the operands.
    </li>
    <li>
      Functions are in the namespace of their module (see <a href="#names">Names and modules</a>): the
      function <code>add</code> of <code>Bitvec</code> is <code>R.Bitvec.add</code>, its rules
      <code>Bitvec.add.r_zero</code>, its spec <code>Bitvec.add.spec</code> and its step
      <code>Bitvec.add.step</code>. The fields of the structures (<code>Ops</code>,
      <code>Ops.Sound</code>), which cannot have a dot, have the flat name,
      <code>bitvec_add</code> (<code>O.bitvec_add</code>), and the primitives and oracles their plain
      name.
    </li>
    <li>
      The arrays of the language are Lean's <code>Array</code>, and their operations
      (<code>arrayLength</code>, <code>arrayGet</code>, <code>arraySet</code>) are defined, with their
      lemmas (reading after a set, lengths, the conversions to and from lists), in
      <code>KanonCore.Array</code>.
    </li>
    <li>
      An <em>arm</em> is one case of a rule, after expanding its or-patterns and the swaps of
      commutative operands; its statement is over the variables of its pattern, with its guard as a
      hypothesis (<code>f.r_name.arm.Stmt</code>). An arm is named after the choices that produced
      it, so that reordering patterns does not rename it: the head constructor (or operator) of each
      or-pattern branch taken, with an index when both branches have the same head
      (<code>lt_leq</code>, <code>lt1</code>), and <code>swap</code> for a swap (numbered when there
      are several), prefixed by <code>cN</code> when the rule has several cases; an arm with no choice
      is <code>main</code>.
    </li>
    <li>
      An arm that only swaps commutative operands is proved from the unswapped one, if its guard and
      body do not depend on the swaps: by the commutativity of the operators swapped
      (<code>Op2.Plus.comm.ok</code>), with <code>kanon_congr</code> for the operands swapped below
      the spec (and for the sort of a spec that is that of an operand, <code>type_of v1</code>, which
      its typing makes equal to that of the other one, by <code>kanon_congr_side</code>).
    </li>
    <li>
      Subsorts are erased in the types and typings, and have a meaning in the statements only through
      <a href="#on-sorts"><code>{`[@lean "P"]{:kanon}`}</code></a>: <code>R.P : Term → Prop</code> is
      written by hand, in a module that <code>R.Statements</code> imports, <code>R.Semantics</code>
      (<code>{`def Nonzero (t : Term) : Prop := ∀ ρ z, eval ρ t = some (.int z) → z ≠ 0{:lean}`}</code>).
      A subsort without it assumes and proves nothing. Kanon trusts the subsorts everywhere else, so
      what <code>P</code> says is only checked by what proves the results of the rule functions. A
      rule function whose spec is a node with an operand <code>v</code> at a subsort position is
      stated for the terms that satisfy <code>P</code>: <code>Nonzero v →</code> before the guard of
      its rules and arms, in <code>Ops.Sound</code>, in its step lemma and in its lifting lemma, where
      it is on the arguments of the call. The elements of a list of operands each satisfy it
      (<code>∀ y ∈ vs, P y</code>). One whose node has a subsort for its result must prove that what
      it returns, a rule or, when none fires, its spec, satisfies <code>P</code>:
      <code>Statements.lean</code> states <code>f.post.main.Stmt</code>
      (<code>∀ O, O.Sound → ∀ args, hyps → P (f.step O args)</code>), which
      <code>kanon_proof%</code> proves only from a hand-written proof
      (<code>{`@[kanon_arm] theorem … : f.post.main.Stmt{:lean}`}</code>).
    </li>
  </ul>

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

  <Heading level={2} id="bool-module">The bool module</Heading>
  <p>
    <code>modules/bool.knl</code> and <code>modules/bool.kn</code> are an optional module of
    booleans: boolean literals, <code>Not</code>, <code>And</code>, <code>Or</code>, equality
    (<code>Eq</code>), conditionals (<code>Ite</code>) and <code>Distinct</code>, with their rules
    (the rule functions <code>Bool.not_</code>, <code>and_</code>, <code>or_</code>,
    <code>ite</code>, <code>eq</code>, <code>eq_untyped</code> and <code>distinct</code>). It is
    built into <code>kanon</code>, as the module that <code>{`use builtin "bool"{:kanon}`}</code>
    uses. The modules above it can add rules to its rule functions with <code>extend rule</code>, and
    literals to its helper <code>sure_neq</code> with <code>extend fn</code>. It is the bool module
    of Soteria's <code>Bv_values</code> and <code>Tiny_values</code>. Its Lean rules are proved once,
    by the library (see <a href="proving.html#boolmod">KanonCore.BoolMod</a>).
  </p>

  <Heading level={2} id="lsp">Language server</Heading>
  <p>
    <code>kanon lsp</code> is a language server (LSP, over standard input and output) for editors.
    As files are edited, it checks the whole language they belong to, as <code>kanon</code> does, and
    reports its errors on the files where they are: all the errors of the functions of a module once
    their signatures are known, and of the independent items of a declaration, rather than only the
    first. It knows the names of the language, as Kanon scopes them:
  </p>
  <ul>
    <li>
      the global names: functions, primitives (written plain in their module, and qualified,
      <code>Bitvec.add</code>, from another one, which renaming changes after the dot), nodes,
      constructors, types, rules (<code>before r</code> goes to the rule <code>r</code> of the
      extended function, or to the law that derives it, <code>{`[@unit 0]{:kanon}`}</code>) and
      operators (<code>+</code>, <code>&amp;&amp;</code>, <code>not</code>, <code>urem</code>, …,
      which go to their <code>infix</code> or <code>prefix</code> declaration, and whose hover says
      what they build, match and compute);
    </li>
    <li>
      the local names: parameters, operands of specs (<code>v1</code> in
      <code>{`And (v1, v2){:kanon}`}</code>), variables of sorts (<code>sz</code> in
      <code>{`(v : TBitVector sz){:kanon}`}</code>, <code>n</code> in a typing), pattern variables
      (<code>x</code>, <code>#x</code>, <code>p as x</code>; a variable bound twice, or in each
      alternative of an or-pattern, is bound where it first appears), <code>let</code>s and the
      arguments of nodes in their typings.
    </li>
  </ul>
  <p>
    It gives their definitions; hovers with the header of a definition and the comment above it, or
    with what a local is (its type, when the source gives it) and where it is bound; their references
    and highlights (of a global, in the files of the language); their renaming, which refuses
    operators, keywords, the names of the built-in modules and invalid new names (a function, a type
    or a rule starts with a lowercase letter, a constructor with an uppercase one, and a function may
    not take the name of another of its module); completion of the names of the language (the names
    of the module of the file plain, those of other modules qualified, and after
    <code>Bitvec.</code> those of <code>Bitvec</code>); and the symbols of a file and of the
    workspace.
  </p>
  <p>
    A <code>.kn</code> file is only meaningful in its language: the server checks a file with each
    <em>root</em> of the workspace that uses it, the <code>.knl</code> files that no other file uses
    (e.g. <code>lang.knl</code>), as <code>kanon ocaml lang.knl</code>; a file that no root uses is
    checked with the only root of its directory, or else alone. In Kanon's own repository,
    <code>modules/</code> stands for the built-in modules, so that they are checked with the
    languages that use them. The files of the workspace are found when it is opened (or a folder
    added), then from the files the editor opens, saves and, if it can watch files
    (<code>workspace/didChangeWatchedFiles</code>), creates and deletes.
  </p>
  <p>
    Limitations: the names come from the last parse of a file, so a file with a syntax error only has
    its global names and operators, found by their text; rename is then refused. The fields of
    records are not names. <code>extend</code> cases see the parameters of the function they extend,
    but not its other locals. A rule derived from a law has no source, so <code>before</code> it goes
    to the law (and the checker rejects it, as the derived rules are added after the
    <code>extend</code>s).
  </p>
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
