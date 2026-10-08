Names that Lean reads as keywords are quoted in the Lean files, in a position
where Lean reads the quotes: a name that follows a prefix is not quoted, as
`r_«at»` is the name `r_` and then `«at»`.

A rule named after a keyword has the rule function `r_at`, with the arms and
the soundness theorems of its name:

  $ cat > lang.knl <<'KN'
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Neg : TInt -> TInt
  > KN
  $ cat > rules.kn <<'KN'
  > rule neg : Neg v =
  >   | at: Neg x -> x
  > KN
  $ kanon lean-all out lang.knl
  $ grep -rhoE 'Rules\.neg\.r_[^ .]*' out | sort -u
  Rules.neg.r_at
  Rules.neg.r_default

The primed parameters of a lifting lemma (`from'`) are quoted as their name is,
not as a prefix of it (`«from»'` is a quoted name and a quote):

  $ cat > lang2.knl <<'KN'
  > use "rules2"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Add : TInt -> TInt -> TInt
  > KN
  $ cat > rules2.kn <<'KN'
  > rule add : Add (from, at) =
  >   | zero: x, 0 -> x
  > KN
  $ kanon lean-all out2 lang2.knl
  $ grep -h -A4 'theorem lift_' out2/Kanon/Rules2/Lift.lean
  theorem lift_rules2_add (hO : O.Sound) {«from» from' : S.Term} {«at» at' : S.Term}
    (h_from : S.Refines «from» from')
    (h_at : S.Refines «at» at') :
    S.Refines (Kanon.Rules2.Rules2.add.spec «from» «at») (O.rules2_add from' at') :=
    Kanon.Sem.Refines.trans (Kanon.Sem.Refines.of_WT fun kw => by

All the words that Lean reserves are quoted, not only the common ones:

  $ cat > lang3.knl <<'KN'
  > use "kw"
  > sort TInt
  > node Int of int : TInt
  > KN
  $ cat > kw.kn <<'KN'
  > fn f (exists forall include repeat sorry : int) (try : int) : int =
  >   let while = exists + forall in
  >   while + include + repeat + sorry + try
  > KN
  $ kanon lean-model lang3.knl | grep -A2 "def Kw.f"
  def Kw.f («exists» : Int) («forall» : Int) («include» : Int) («repeat» : Int) («sorry» : Int) («try» : Int) : Int :=
    (let «while» := («exists» + «forall»);
    ((((«while» + «include») + «repeat») + «sorry») + «try»))

The fields of a record are quoted in its declaration, in its literals and in
the access to a field:

  $ cat > lang4.knl <<'KN'
  > use "rec"
  > sort TInt
  > node Int of int : TInt
  > type span = { from : int; to_ : int }
  > KN
  $ cat > rec.kn <<'KN'
  > fn mk (a b : int) : span = { from = a; to_ = b }
  > fn start (s : span) : int = s.from
  > KN
  $ kanon lean-types lang4.knl | grep -A2 "^structure"
  structure Span where
    «from» : Int
    to_ : Int
  $ kanon lean-model lang4.knl | grep -A1 "^def Rec\.\(mk\|start\)"
  def Rec.mk (a : Int) (b : Int) : Kanon.Span :=
    ({ «from» := a, to_ := b } : Kanon.Span)
  --
  def Rec.start (s : Kanon.Span) : Int :=
    s.«from»

The same goes for a module named after a keyword, in the names of the theorems
about its nodes:

  $ cat > lang5.knl <<'KN'
  > use "open"
  > sort TInt
  > node Int of int : TInt
  > KN
  $ cat > open.knl <<'KN'
  > sort TOpen
  > node Op : TOpen -> TOpen
  > KN
  $ kanon lean-semantics lang5.knl | grep -o "\(WT\|ev\)_[^ ]*open[^ ]*" | sort -u
  WT_open
  ev_open

The arguments of the second node of `Rel` are those of the first, with primes,
and are new variables even if the first has an argument named so:

  $ cat > lang6.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > node Mk of int * int (x, x') : TInt
  > node Pair of t * t (a, a') : TInt
  > KN
  $ kanon lean-node lang6.knl | grep -A3 "^def Rel"
  def Rel (R : T → U → Prop) : Node T → Node U → Prop
    | (.Int x1), (.Int x1') => x1 = x1'
    | (.Mk x x'), (.Mk x'' x''') => x = x'' ∧ x' = x'''
    | (.Pair a a'), (.Pair a'' a''') => R a a'' ∧ R a' a'''

The arguments of a node are variables of the Lean files, in which the names
that those files use themselves (`f`, the function of `Node.map`, `y`, the
element of `Node.All`, `ev` and the like in `Semantics.lean`) are not
supported:

  $ for n in f y ev evList allList; do
  >   printf 'sort TInt\nnode Int of int : TInt\nnode Seq of t list (%s) : TInt\n' $n > lang7.knl
  >   kanon lean-node lang7.knl 2>&1
  > done
  lang7.knl:3:5: the name f of an argument of Seq: not supported in Lean
  lang7.knl:3:5: the name y of an argument of Seq: not supported in Lean
  lang7.knl:3:5: the name ev of an argument of Seq: not supported in Lean
  lang7.knl:3:5: the name evList of an argument of Seq: not supported in Lean
  lang7.knl:3:5: the name allList of an argument of Seq: not supported in Lean
  [1]

The parameters of a rule function are bound in its theorems, with the
hypotheses `h` and `hO`, the result `res` and the semantics `sem`, whose names
they may not have:

  $ for n in h hO res sem; do
  >   printf 'use "rules9"\nsort TInt\nnode Int of int : TInt\nnode Add : TInt -> TInt -> TInt\n' > lang9.knl
  >   printf 'rule add : Add (%s, v)\n' $n > rules9.kn
  >   kanon lean-model lang9.knl 2>&1 | head -1
  > done
  ./rules9.kn:1:0: the parameter h of the rule function Rules9.add: not supported in Lean
  ./rules9.kn:1:0: the parameter hO of the rule function Rules9.add: not supported in Lean
  ./rules9.kn:1:0: the parameter res of the rule function Rules9.add: not supported in Lean
  ./rules9.kn:1:0: the parameter sem of the rule function Rules9.add: not supported in Lean

The typing of a node whose sort takes sorts (`TPair of ty * ty`) applies the
sorts of its operands to the constructor in parentheses, and quantifies sort
variables over `Ty`, the sorts of the language:

  $ cat > lang10.knl <<'KN'
  > sort TInt
  > sort TPair of ty * ty
  > node Int of int : TInt
  > node MkPair : a -> b -> TPair (a, b)
  > node Fst : TPair (a, b) -> a
  > node Swap : TPair (a, b) -> TPair (b, a)
  > KN
  $ kanon lean-lang lang10.knl | sed -n '/^def Node.wt/,/^$/p'
  def Node.wt {T Ty : Type} (sLang10 : (Kanon.Srt Ty) → Ty) (ty : T → Ty) : Node T → Ty → Prop
    | (.Int x1), t => (t = (sLang10 .TInt))
    | (.MkPair a1 a2), t => (t = (sLang10 (.TPair (ty a1) (ty a2))))
    | (.Fst a1), t => (∃ a : Ty, (∃ b : Ty, ty a1 = (sLang10 (.TPair a b))) ∧ t = a)
    | (.Swap a1), t => (∃ a b : Ty, ty a1 = (sLang10 (.TPair a b)) ∧ t = (sLang10 (.TPair b a)))
  

In the typing of the nodes, `Node.wt`, a node named after a Lean type (`Int`)
is in scope: the types of the variables and numbers are then `_root_.Int`:

  $ cat > lang11.knl <<'KN'
  > sort TW of nat
  > node Int of int : TW n
  > node WExt of nat (k) : TW n -> TW (n + k) when 0 <= k
  > KN
  $ kanon lean-lang lang11.knl | sed -n '/^def Node.wt/,/^$/p'
  def Node.wt {T Ty : Type} (sLang11 : Kanon.Srt → Ty) (ty : T → Ty) : Node T → Ty → Prop
    | (.Int x1), t => ((∃ n : _root_.Int, 0 < n ∧ t = (sLang11 (.TW n))))
    | (.WExt k a2), t => (∃ n : _root_.Int, 0 < n ∧ ty a2 = (sLang11 (.TW n)) ∧ (0 : _root_.Int) ≤ k ∧ t = (sLang11 (.TW (n + k))))
  

The same goes for the functions of `Node` (`All`, `Rel`, `children`), with
nodes named `True`, `False` and `List`:

  $ cat > lang12.knl <<'KN'
  > sort TB
  > node True : TB
  > node False : TB
  > node List of t list : TB
  > KN
  $ kanon lean-node lang12.knl | sed -n '/^def All/,/^theorem all_iff/p'
  def All (P : T → Prop) : Node T → Prop
    | .True => _root_.True
    | .False => _root_.True
    | (.List l1) => (∀ y ∈ l1, P y)
  
  /-- The nodes have the same arguments, and their children are related by `R`. -/
  def Rel (R : T → U → Prop) : Node T → Node U → Prop
    | .True, .True => _root_.True
    | .False, .False => _root_.True
    | (.List l1), (.List l1') => Kanon.Forall₂ R l1 l1'
    | _, _ => _root_.False
  
  /-- The children of the node, in order. -/
  def children : Node T → _root_.List T
    | .True => []
    | .False => []
    | (.List l1) => l1
  
  /-- Every child of the node satisfies `P` when all its children do. -/
  theorem all_iff (P : T → Prop) (n : Node T) : n.All P ↔ ∀ c ∈ n.children, P c := by

A pattern variable that has the name of another parameter (`v1` for the second
operand, `v2` for the first) is rejected: the statements of the arm name the
parameters and the pattern variables alike.

  $ cat > lang13.knl <<'KN'
  > use "rules13"
  > sort TInt
  > node Int of int : TInt
  > node Sub : TInt -> TInt -> TInt
  > KN
  $ cat > rules13.kn <<'KN'
  > rule sub : Sub (v1, v2) =
  >   | crossed: v2, v1 -> v1
  > KN
  $ kanon lean-statements lang13.knl > /dev/null
  ./rules13.kn:2:13: Rules13.sub: pattern variable v2 shadows a parameter
  [1]

So is the name of an `as` variable:

  $ cat > rules13.kn <<'KN'
  > rule sub : Sub (v1, v2) =
  >   | crossed: (Int a as v2), x -> v2
  > KN
  $ kanon lean-statements lang13.knl > /dev/null
  ./rules13.kn:2:13: Rules13.sub: pattern variable v2 shadows a parameter
  [1]

The functions of `Semantics.lean` on the nodes of a module are named after it
(`allList`, `evList` for a module named `List`), and so are those on the lists
of children, so a module `List` with such nodes is not supported:

  $ cat > lang14.knl <<'KN'
  > use "list"
  > sort TInt
  > node Int of int : TInt
  > KN
  $ cat > list.knl <<'KN'
  > sort TL
  > node Cons : t list -> TL
  > KN
  $ kanon lean-semantics lang14.knl > /dev/null
  kanon: the module List: its functions allList and evList are those of the lists of children: not supported in Lean
  [1]

A rule function without parameters (the spec is a node without arguments) has
no `∀` and no `fun` in the statements and the model of the language:

  $ cat > lang15.knl <<'KN'
  > use "rules15"
  > sort TInt
  > node Int of int : TInt
  > node Zero : TInt
  > KN
  $ cat > rules15.kn <<'KN'
  > rule zero : Zero
  > KN
  $ kanon lean-model lang15.knl | grep "rules15_zero :"
    rules15_zero : S.Term
    rules15_zero : S.Refines (Rules15.zero.spec ) (O.rules15_zero )
  $ kanon lean-rules lang15.knl | grep "rules15_zero :="
      rules15_zero := Kanon.Rules15.Rules15.zero.spec (S := sem)  }
      rules15_zero := Rules15.zero.step O }
      { rules15_zero := Kanon.Sem.Refines.refl }
      { rules15_zero := Rules15.zero.step_sound _ hO }

A helper without parameters that needs the record `O` of the model is applied
to it in parentheses, as an argument:

  $ cat > lang16.knl <<'KN'
  > use "rules16"
  > KN
  $ cat > rules16.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Plus : TInt -> TInt -> TInt
  > infix "+" = Plus, plus
  > KN
  $ cat > rules16.kn <<'KN'
  > rule plus : Plus (v1, v2)
  > fn two : t = Int 1 + Int 1
  > fn use_two (x : t) : t = x + two
  > KN
  $ kanon lean-model lang16.knl | grep -A1 "def Rules16.use_two"
  def Rules16.use_two (O : Ops S) (x : S.Term) : S.Term :=
    (O.rules16_plus x (Kanon.Rules16.Rules16.two O))

The primed parameters of a lifting lemma are not parameters of the rule
function, even if it has parameters `x` and `x'`:

  $ cat > lang17.knl <<'KN'
  > use "rules17"
  > KN
  $ cat > rules17.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > node Plus : TInt -> TInt -> TInt
  > KN
  $ cat > rules17.kn <<'KN'
  > rule plus : Plus (x, x')
  > KN
  $ kanon lean-statements lang17.knl | grep -A3 "theorem lift_" | head -4
  theorem lift_rules17_plus (hO : O.Sound) {x x'' : S.Term} {x' x''' : S.Term}
    (h_x : S.Refines x x'')
    (h_x' : S.Refines x' x''') :
    S.Refines (Kanon.Rules17.Rules17.plus.spec x x') (O.rules17_plus x'' x''') :=

A node named `All` or `Rel` would be declared twice in `Node`, with its functions
of those names, and a node named `Node` or `Lang` hides the type `Node` and the
class `Lang` in the declarations about the nodes:

  $ for n in All Rel Node Lang; do
  >   printf 'sort TInt\nnode Int of int : TInt\nnode %s : TInt -> TInt\n' $n > lang18.knl
  >   kanon lean-node lang18.knl 2>&1 | head -1
  > done
  lang18.knl:3:5: the node All, a name of the Lean files of its module: not supported in Lean
  lang18.knl:3:5: the node Rel, a name of the Lean files of its module: not supported in Lean
  lang18.knl:3:5: the node Node, a name of the Lean files of its module: not supported in Lean
  lang18.knl:3:5: the node Lang, a name of the Lean files of its module: not supported in Lean

The data types of a module are declared in its namespace, beside the sorts
(`Srt`), the class `Lang` and the other declarations of its files, and beside
those of the language (`Term`, `Refines`, `Val`, `Env`) and of Kanon's library
(`Sem`, `Dom`, ...) in the root `Kanon`, so a type may not have their names, nor
those of the classes that it derives, nor Lean's keywords. `[@lean "N"]` names
it otherwise:

  $ for n in srt ops lang typed values term refines val env sem dom embed repr inhabited decidable_eq prop; do
  >   printf 'type %s = A | B\nsort TInt\nnode Int of int : TInt\nnode Col of %s : TInt\n' $n $n > lang19.knl
  >   kanon lean-types lang19.knl 2>&1 | head -1
  > done
  lang19.knl:1:5: the type srt, whose Lean name Srt is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type ops, whose Lean name Ops is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type lang, whose Lean name Lang is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type typed, whose Lean name Typed is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type values, whose Lean name Values is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type term, whose Lean name Term is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type refines, whose Lean name Refines is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type val, whose Lean name Val is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type env, whose Lean name Env is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type sem, whose Lean name Sem is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type dom, whose Lean name Dom is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type embed, whose Lean name Embed is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type repr, whose Lean name Repr is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type inhabited, whose Lean name Inhabited is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type decidable_eq, whose Lean name DecidableEq is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  lang19.knl:1:5: the type prop, whose Lean name Prop is declared elsewhere (name it with [@lean "N"]): not supported in Lean
  $ printf 'type srt [@lean "Shape"] = A | B\nsort TInt\nnode Int of int : TInt\nnode Col of srt : TInt\n' > lang20.knl
  $ kanon lean-types lang20.knl | grep inductive
  inductive Shape where

A module that declares a type of its own name has the functions of the module
in the namespace of the type, where the fields of a record are declared:

  $ cat > lang21.knl <<'KN'
  > use "span"
  > sort TInt
  > node Int of int : TInt
  > KN
  $ echo 'type span = { lo : int; hi : int }' > span.knl
  $ echo 'fn lo (x : int) : int = x' > span.kn
  $ kanon lean-model lang21.knl 2>&1 | head -1
  ./span.kn:1:0: the function lo, a field of the record type span of its module: not supported in Lean

The names of the language are also those of a module that has rule functions
(the steps of its rules are in its namespace):

  $ cat > lang22.knl <<'KN'
  > [@@@lean_root "Ex"]
  > use "m"
  > sort TInt
  > node Int of int : TInt
  > KN
  $ echo 'type term = A | B' > m.knl
  $ echo 'fn f (x : int) : int = x' > m.kn
  $ kanon lean-types lang22.knl 2>&1 | head -1
  ./m.knl:1:5: the type term, whose Lean name Term is declared elsewhere (name it with [@lean "N"]): not supported in Lean

The proof of an arm that commutativity derives from another one introduces the
hypothesis on the model and the one on the guard under names of its own, so
that pattern variables may be named `hO` and `hg`:

  $ cat > lang25.knl <<'KN'
  > use "rules25"
  > sort TInt
  > node Int of int : TInt
  > node Neg : TInt -> TInt
  > node Plus : TInt -> TInt -> TInt [@comm]
  > notation Int
  > infix "+" = Plus, plus
  > KN
  $ cat > rules25.kn <<'KN'
  > rule plus : Plus (v1, v2) =
  >   | unit: Neg hO + Int hg when hg = 0 -> Neg hO
  > KN
  $ kanon lean-soundness lang25.knl | grep "intro S\|ok O kanon"
    intro S _ _ O kanon__hO hg t__5 hO t__3 kanon__hg
      (Rules25.plus.r_unit.main.ok O kanon__hO hO t__3 hg t__5 kanon__hg)
