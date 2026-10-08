A subsort is a sort of the same arguments as its parent, which a node may use
in its typing: `subsort TNonzero of nat : TBitVector n`. It has no constructor
of its own and no other meaning in OCaml: the generated types and rules are
those of the parent, so that a subsort in a typing is the sort of its parent.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > use "rules"
  > sort TBitVector of nat [@get Rules.size]
  > subsort TNonzero of nat : TBitVector n
  > subsort TZero of nat : TBitVector n
  > sort TBool
  > node BitVec of int * nat (v, n) : TBitVector n
  > node Zero of nat (n) : TZero n
  > node Div of bool : TBitVector n -> TNonzero n -> TBitVector n
  > node Ult : TBitVector n -> TBitVector n -> TBool
  > KN
  $ cat > rules.kn <<'KN'
  > prim size : t -> int
  > rule bv_div : Div (signed, v1, v2)
  > KN
  $ kanon ocaml out lang.knl && cat out/Generated/types.ml | sed -n '/^type kind/,/^and t =/p'
  type kind =
    | BitVec of Z.t * int
    | Zero of int
    | Op2 of op2 * t * t
  
  and op2 =
    | Div of bool
    | Ult
  
  and ty =
    | TBitVector of int
    | TBool
  
  and t = {
  $ kanon ocaml out lang.knl && cat out/Generated/rules.ml | sed -n '/let rules_bv_div/,/^$/p'
    let rules_bv_div (signed : bool) (v1 : t) (v2 : t) : t =
        (assert ((match v1.ty, v2.ty with
                 | ((TBitVector (kanon__n)), (TBitVector (kanon__s1)))
                   when (let kanon__n = Z.of_int kanon__n in
                   let kanon__s1 = Z.of_int kanon__s1 in
                   ((Z.equal kanon__s1 kanon__n))) ->
                   true
                 | _ -> false
                 ) [@warning "-11"]);
        (match v1, v2 with
        | _ -> (node (Op2 ((Div (signed)), v1, v2)) v1.ty)
        ))
  end
  

The checks of a subsort declaration: its arguments are those of its parent
sort, which it applies to variables, and it is the sort of an operand or of a
result only.

  $ check() { printf '%s\n' 'sort TBitVector of nat' 'sort TBool' "$@" > bad.knl; : > bad.kn; kanon ocaml out bad.knl bad.kn; }
  $ check 'subsort A of int : TBitVector n'
  bad.knl:3:8: subsort A: its arguments must be those of TBitVector (nat)
  [1]
  $ check 'subsort A of nat : TBitVector 32'
  bad.knl:3:19: subsort A: its parent TBitVector must be applied to the arguments of the subsort, as distinct variables
  [1]
  $ check 'subsort A of nat * nat : TBitVector (n, n)'
  bad.knl:3:8: subsort A: its arguments must be those of TBitVector (nat)
  [1]
  $ check 'subsort A of nat : TBool'
  bad.knl:3:8: subsort A: its arguments must be those of TBool (none)
  [1]
  $ check 'subsort A of nat : TBitVector n' 'subsort B of nat : A n'
  bad.knl:4:19: A is a subsort: the parent of a subsort is a sort
  [1]
  $ check 'subsort A of nat : TSeq n'
  bad.knl:3:19: unknown sort TSeq
  [1]
  $ check 'subsort A of nat (n) : TBitVector n'
  bad.knl:3:17: subsort A: a subsort has no argument names nor condition: its arguments are those of its parent
  [1]
  $ check 'subsort A of nat'
  bad.knl:3:8: subsort A: expected its parent sort: subsort A of args : Parent args
  [1]
  $ check 'subsort A of nat : TBitVector n [@foo]'
  bad.knl:3:34: unknown attribute [@foo]
  [1]
  $ check 'subsort TBitVector of nat : TBitVector n'
  bad.knl:3:8: subsort TBitVector is declared twice
  [1]
  $ check 'subsort A of nat : TBitVector n' 'subsort A of nat : TBitVector n'
  bad.knl:4:8: subsort A is declared twice
  [1]
  $ check 'subsort A of nat : TBitVector n' 'node Foo : TBitVector (A n) -> TBool'
  bad.knl:4:23: A is a subsort: it is the sort of an operand or of a result, not an argument of a sort
  [1]

Lean: a subsort is erased in the typing (`Lang.lean`, `Syntax.lean`, ...), and
has a meaning only if it names a Lean predicate on terms, `[@lean "P"]`, which
the hand-written `Prims.lean` of its module defines. Then the statements of a
rule function assume `P` of the operand at a position of the subsort (of each
element of a list of operands), as an hypothesis before its guard; and a rule
function whose result has the subsort must prove that what it returns, a rule
or its spec, satisfies it (`f.r.main.post.Stmt` and `f.spec_post.Stmt`). A
subsort without a predicate assumes and proves nothing.

  $ cat > nonzero.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > use "nonzero_rules"
  > sort TBitVector of nat [@get Nonzero_rules.size]
  > subsort TNonzero of nat : TBitVector n [@lean "Nonzero"]
  > subsort TZero of nat : TBitVector n
  > node Div of bool : TBitVector n -> TNonzero n -> TBitVector n
  > node Pos : TBitVector n -> TNonzero n
  > node Every : (TNonzero 8) list -> TBitVector 8
  > node Mod : TBitVector n -> TZero n -> TBitVector n
  > KN
  $ cat > nonzero_rules.kn <<'KN'
  > prim size : t -> int
  > rule bv_div : Div (s, v1, v2) =
  >   | self: x, y when x = y -> v1
  > rule pos : Pos v
  > rule all : Every vs
  > rule bv_mod : Mod (v1, v2)
  > KN
  $ kanon lean out nonzero.knl
  $ sed -n '/^structure Ops.Sound.*where/,/^$/p' out/Generated/Kanon/Nonzero_rules/Model.lean
  structure Ops.Sound (O : Ops S) : Prop extends toNonzeroSound : Kanon.Ops.Sound O.toNonzeroOps where
    nonzero_rules_bv_div : ∀ (s : Bool) (v1 : S.Term) (v2 : S.Term), Kanon.Nonzero v2 → S.Refines (Nonzero_rules.bv_div.spec s v1 v2) (O.nonzero_rules_bv_div s v1 v2)
    nonzero_rules_pos : ∀ (v : S.Term), S.Refines (Nonzero_rules.pos.spec v) (O.nonzero_rules_pos v)
    nonzero_rules_pos_post : ∀ (v : S.Term), Kanon.Nonzero (O.nonzero_rules_pos v)
    nonzero_rules_all : ∀ (vs : (List S.Term)), (∀ y ∈ vs, Kanon.Nonzero y) → S.Refines (Nonzero_rules.all.spec vs) (O.nonzero_rules_all vs)
    nonzero_rules_bv_mod : ∀ (v1 : S.Term) (v2 : S.Term), S.Refines (Nonzero_rules.bv_mod.spec v1 v2) (O.nonzero_rules_bv_mod v1 v2)
  
  $ cat out/Generated/Kanon/Nonzero_rules/Lift.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/bv_div.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/pos.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/all.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/bv_mod.lean | sed -n '/r_self.main.Stmt/,/^$/p;/^def Nonzero_rules.all.r_default.main/,/^$/p;/^def Nonzero_rules.bv_mod.r_default.main/,/^$/p'
  def Nonzero_rules.bv_div.r_self.main.Stmt : Prop :=
    ∀ {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S), O.Sound →
    ∀ (s : Bool) (v1 : S.Term) (v2 : S.Term),
    Kanon.Nonzero v2 →
    (decide (v1 = v2)) = true →
    S.Refines (Kanon.Nonzero_rules.Nonzero_rules.bv_div.spec s v1 v2)
    (v1)
  
  def Nonzero_rules.all.r_default.main.Stmt : Prop :=
    ∀ {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S), O.Sound →
    ∀ (vs : (List S.Term)),
    (∀ y ∈ vs, Kanon.Nonzero y) →
    S.Refines (Kanon.Nonzero_rules.Nonzero_rules.all.spec vs)
    ((Kanon.mk (.Every vs) (Kanon.sort (.TBitVector (8 : Int)))))
  
  def Nonzero_rules.bv_mod.r_default.main.Stmt : Prop :=
    ∀ {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S), O.Sound →
    ∀ (v1 : S.Term) (v2 : S.Term),
    S.Refines (Kanon.Nonzero_rules.Nonzero_rules.bv_mod.spec v1 v2)
    ((Kanon.mk (.Mod v1 v2) (S.ty v1)))
  

The proofs thread the hypotheses: the proofs of the rules and of the functions
take them, the lifting lemma needs them on the arguments of the call, and the
proof of the arms that are derived by commutativity is not derived when there
are some. The post-condition has a proof that the language gives:

  $ cat out/Generated/Kanon/Nonzero_rules/Soundness/Nonzero_rules/bv_div.lean out/Generated/Kanon/Nonzero_rules/Soundness/Nonzero_rules/pos.lean out/Generated/Kanon/Nonzero_rules/Soundness/Nonzero_rules/all.lean out/Generated/Kanon/Nonzero_rules/Soundness/Nonzero_rules/bv_mod.lean out/Generated/Kanon/Nonzero_rules/Soundness.lean | grep "hs_\|post"
  theorem Nonzero_rules.bv_div.r_self.sound {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S) (hO : O.Sound) (s : Bool) (v1 : S.Term) (v2 : S.Term) (hs_v2 : Kanon.Nonzero v2) (res : S.Term)
  theorem Nonzero_rules.bv_div.r_default.sound {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S) (hO : O.Sound) (s : Bool) (v1 : S.Term) (v2 : S.Term) (hs_v2 : Kanon.Nonzero v2) (res : S.Term)
  theorem Nonzero_rules.pos.r_default.main.post.ok : Nonzero_rules.pos.r_default.main.post.Stmt :=
    no_implicit_lambda% (kanon_proof% Nonzero_rules.pos.r_default.main.post)
  theorem Nonzero_rules.pos.r_default.post_sound {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S) (hO : O.Sound) (v : S.Term) (res : S.Term)
    · kanon_arm h (Nonzero_rules.pos.r_default.main.post.ok O hO)
  theorem Nonzero_rules.pos.spec_post.ok : Nonzero_rules.pos.spec_post.Stmt :=
    no_implicit_lambda% (kanon_proof% Nonzero_rules.pos.spec_post)
  theorem Nonzero_rules.all.r_default.sound {S : Kanon.Sem} [Kanon.Lang S] [Kanon.Typed S] (O : Ops S) (hO : O.Sound) (vs : (List S.Term)) (hs_vs : (∀ y ∈ vs, Kanon.Nonzero y)) (res : S.Term)
  $ grep "hs_" out/Generated/Kanon/Rules.lean
  theorem Nonzero_rules.bv_div.step_sound (O : Kanon.Nonzero_rules.Ops sem) (hO : O.Sound) (s : Bool) (v1 : Term) (v2 : Term) (hs_v2 : Kanon.Nonzero (S := sem) v2) :
    refine Kanon.Refinement.firstSome_cons (fun res h => Kanon.Nonzero_rules.Nonzero_rules.bv_div.r_self.sound (S := sem) O hO s v1 v2 hs_v2 res h) ?_
    refine Kanon.Refinement.firstSome_cons (fun res h => Kanon.Nonzero_rules.Nonzero_rules.bv_div.r_default.sound (S := sem) O hO s v1 v2 hs_v2 res h) ?_
  theorem Nonzero_rules.all.step_sound (O : Kanon.Nonzero_rules.Ops sem) (hO : O.Sound) (vs : (List Term)) (hs_vs : (∀ y ∈ vs, Kanon.Nonzero (S := sem) y)) :
    refine Kanon.Refinement.firstSome_cons (fun res h => Kanon.Nonzero_rules.Nonzero_rules.all.r_default.sound (S := sem) O hO vs hs_vs res h) ?_
      { nonzero_rules_bv_div := fun s v1 v2 hs_v2 => Kanon.Sem.Refines.refl,
        nonzero_rules_all := fun vs hs_vs => Kanon.Sem.Refines.refl,
  $ cat out/Generated/Kanon/Nonzero_rules/Lift.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/bv_div.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/pos.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/all.lean out/Generated/Kanon/Nonzero_rules/Statements/Nonzero_rules/bv_mod.lean | grep "hs_"
    (h_v2 : S.Refines v2 v2') (hs_v2 : Kanon.Nonzero v2') :
      (hO.nonzero_rules_bv_div s v1' v2' hs_v2)
  theorem lift_nonzero_rules_all (hO : O.Sound) {vs : (List S.Term)} (hs_vs : (∀ y ∈ vs, Kanon.Nonzero y)) :
    hO.nonzero_rules_all vs hs_vs

The Lean files of the other backends do not see subsorts:

  $ grep -c "Nonzero\|TZero" out/Generated/Kanon/Node.lean
  0
  [1]
  $ grep -c "Nonzero\|TZero" out/Generated/Kanon/Syntax.lean
  0
  [1]

A commutative node whose operands have different subsorts is rejected, as
swapping them would swap their assumptions:

  $ check 'subsort A of nat : TBitVector n' 'node Foo : TBitVector n -> A n -> TBitVector n [@comm]'
  bad.knl:4:47: [@comm]: the operands of Foo have different subsorts: swapping them is not sound
  [1]
  $ check 'subsort A of nat : TBitVector n' 'node Foo : A n -> A n -> TBitVector n [@comm]'
