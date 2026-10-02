import KanonCore.BoolMod.Val
import KanonCore.Proof

/-!
# A language that uses the bool module

The rules of the bool module (`modules/bool.kn`) are proved once, in
`KanonCore.BoolMod.Rules`, for any language that gives a `BoolMod.Lang` of its
semantics `S : Kanon.Sem`:

- the terms of the nodes of the module: the kinds of its terms (`Kind`, of
  which `mk k t` is the term at the type `t`), the kinds of the nodes (`litK`,
  `notK`, `andK`, `orK`, `eqK`, `iteK`, `distinctK`), and the type of booleans
  (`tbool`), such that the terms of the generated statements are definitionally
  equal to them (e.g. `Term.mk (Kind.Binop Binop.And a b) Ty.TBool` to
  `mk (andK a b) tbool`);
- the booleans among its values (`vbool`);
- the helper `sure_neq` of the module (which the modules above it extend, so
  it is the language's);
- laws: the typing of the nodes, their evaluation by the operations of
  `KanonCore.BoolMod.Val`, that well-typed booleans evaluate to booleans, and
  what the rules assume of `sure_neq`.

The rules compare terms with `decide (a = b)`, as the generated model does.

The model of the language gives its rule functions, oracles and helpers of the
module as a `BoolMod.Ops` (`Ops.bool`, which Kanon generates in
`Soundness.lean`, with the proof `Ops.Sound.bool` of their properties).
-/

namespace Kanon.BoolMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- A language that uses the bool module, with semantics `S`. -/
structure Lang (S : Sem) where
  make ::
  /-- The kinds of terms. -/
  Kind : Type
  /-- The term of a kind, at a type. -/
  mk : Kind → S.Ty → S.Term
  /-- The type of booleans. -/
  tbool : S.Ty
  litK : Bool → Kind
  notK : S.Term → Kind
  andK : S.Term → S.Term → Kind
  orK : S.Term → S.Term → Kind
  eqK : S.Term → S.Term → Kind
  iteK : S.Term → S.Term → S.Term → Kind
  distinctK : List S.Term → Kind
  /-- The boolean values. -/
  vbool : Bool → S.Val
  /-- The helper `sure_neq` of the module, as extended by the language. -/
  sure_neq : S.Term → S.Term → Bool
  ty_mk : ∀ k t, S.ty (mk k t) = t
  WT_lit : ∀ b t, S.WT (mk (litK b) t) ↔ t = tbool
  WT_not : ∀ a t, S.WT (mk (notK a) t) ↔ S.ty a = tbool ∧ t = tbool ∧ S.WT a
  WT_and : ∀ a b t, S.WT (mk (andK a b) t) ↔
    S.ty a = tbool ∧ S.ty b = tbool ∧ t = tbool ∧ S.WT a ∧ S.WT b
  WT_or : ∀ a b t, S.WT (mk (orK a b) t) ↔
    S.ty a = tbool ∧ S.ty b = tbool ∧ t = tbool ∧ S.WT a ∧ S.WT b
  WT_eq : ∀ a b t, S.WT (mk (eqK a b) t) ↔ S.ty a = S.ty b ∧ t = tbool ∧ S.WT a ∧ S.WT b
  WT_ite : ∀ g a b t, S.WT (mk (iteK g a b) t) ↔
    S.ty g = tbool ∧ S.ty a = t ∧ S.ty b = t ∧ S.WT g ∧ S.WT a ∧ S.WT b
  WT_distinct : ∀ l t, S.WT (mk (distinctK l) t) ↔
    t = tbool ∧ ∃ e, ∀ x ∈ l, S.ty x = e ∧ S.WT x
  ev_lit : ∀ ρ b t, S.ev ρ (mk (litK b) t) = some (vbool b)
  ev_not : ∀ ρ a t, S.ev ρ (mk (notK a) t) = pnot vbool (S.ev ρ a)
  ev_and : ∀ ρ a b t, S.ev ρ (mk (andK a b) t) = pand vbool (S.ev ρ a) (S.ev ρ b)
  ev_or : ∀ ρ a b t, S.ev ρ (mk (orK a b) t) = por vbool (S.ev ρ a) (S.ev ρ b)
  ev_eq : ∀ ρ a b t, S.ev ρ (mk (eqK a b) t) = peq vbool (S.ev ρ a) (S.ev ρ b)
  ev_ite : ∀ ρ g a b t, S.ev ρ (mk (iteK g a b) t) =
    pite vbool (S.ev ρ g) (S.ev ρ a) (S.ev ρ b)
  ev_distinct : ∀ ρ l t, S.ev ρ (mk (distinctK l) t) = pdistinct vbool (l.mapM (S.ev ρ))
  /-- Well-typed booleans evaluate to booleans. -/
  ev_bool : ∀ ρ t v, S.WT t → S.ty t = tbool → S.ev ρ t = some v → ∃ b, v = vbool b
  vbool_inj : Function.Injective vbool
  /-- Surely different terms of the same type have different values. -/
  sure_neq_sound : ∀ ρ a b u, sure_neq a b = true → S.ty a = S.ty b → S.WT a → S.WT b →
    S.ev ρ a = some u → S.ev ρ b = some u → False

namespace Lang

variable {S : Sem} (L : Lang S)

/-! ## The specs of the rule functions, and the literals -/

abbrev vtrue : S.Term := L.mk (L.litK true) L.tbool
abbrev vfalse : S.Term := L.mk (L.litK false) L.tbool
abbrev of_bool (b : Bool) : S.Term := if b then L.vtrue else L.vfalse
abbrev mkNot (a : S.Term) : S.Term := L.mk (L.notK a) L.tbool
abbrev mkAnd (a b : S.Term) : S.Term := L.mk (L.andK a b) L.tbool
abbrev mkOr (a b : S.Term) : S.Term := L.mk (L.orK a b) L.tbool
abbrev mkEq (a b : S.Term) : S.Term := L.mk (L.eqK a b) L.tbool
abbrev mkIte (g a b : S.Term) : S.Term := L.mk (L.iteK g a b) (S.ty a)
abbrev mkDistinct (l : List S.Term) : S.Term := L.mk (L.distinctK l) L.tbool

variable {L}

theorem vbool_eq_iff {a b : Bool} : L.vbool a = L.vbool b ↔ a = b := L.vbool_inj.eq_iff

/-- The values of a well-typed boolean. -/
theorem ev_cases {ρ : S.Env} {t : S.Term} (w : S.WT t) (h : S.ty t = L.tbool) :
    S.ev ρ t = none ∨ S.ev ρ t = some (L.vbool true) ∨ S.ev ρ t = some (L.vbool false) := by
  rcases e : S.ev ρ t with _ | v
  · exact .inl rfl
  · obtain ⟨b, rfl⟩ := L.ev_bool ρ t v w h e
    cases b <;> simp

/-- The values of any term. -/
theorem ev_opt {ρ : S.Env} {t : S.Term} : S.ev ρ t = none ∨ ∃ v, S.ev ρ t = some v := by
  cases S.ev ρ t <;> simp

/-! ## Congruence -/

theorem refines_not {a a' : S.Term} {t : S.Ty} (ha : S.Refines a a') :
    S.Refines (L.mk (L.notK a) t) (L.mk (L.notK a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [L.WT_not] at w
    obtain ⟨wa, sa⟩ := ha.syn w.2.2
    exact ⟨(L.WT_not _ _).2 ⟨sa.trans w.1, w.2.1, wa⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.WT_not] at w
    rw [L.ev_not] at e ⊢
    exact pnot_mono (ha.ev w.2.2 ρ) v e

theorem refines_and {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (L.mk (L.andK a b) t) (L.mk (L.andK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_and] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2.2
    exact ⟨(L.WT_and _ _ _).2 ⟨sa.trans w.1, sb.trans w.2.1, w.2.2.1, wa, wb⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.ev_and] at e ⊢
    exact pand_mono (ha.ev w.2.2.2.1 ρ) (hb.ev w.2.2.2.2 ρ) v e

theorem refines_or {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (L.mk (L.orK a b) t) (L.mk (L.orK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_or] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2.2
    exact ⟨(L.WT_or _ _ _).2 ⟨sa.trans w.1, sb.trans w.2.1, w.2.2.1, wa, wb⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.ev_or] at e ⊢
    exact por_mono (ha.ev w.2.2.2.1 ρ) (hb.ev w.2.2.2.2 ρ) v e

theorem refines_eq {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (L.mk (L.eqK a b) t) (L.mk (L.eqK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_eq] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2
    exact ⟨(L.WT_eq _ _ _).2 ⟨by rw [sa, sb]; exact w.1, w.2.1, wa, wb⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.ev_eq] at e ⊢
    exact peq_mono (ha.ev w.2.2.1 ρ) (hb.ev w.2.2.2 ρ) v e

theorem refines_ite {g g' a a' b b' : S.Term} {t t' : S.Ty} (hg : S.Refines g g')
    (ha : S.Refines a a') (hb : S.Refines b b') (ht : S.WT (L.mk (L.iteK g a b) t) → t' = t) :
    S.Refines (L.mk (L.iteK g a b) t) (L.mk (L.iteK g' a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ht := ht w
    subst ht
    rw [L.WT_ite] at w
    obtain ⟨h1, h2, h3, wg, wa, wb⟩ := w
    obtain ⟨wg', sg⟩ := hg.syn wg
    obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨(L.WT_ite _ _ _ _).2 ⟨sg.trans h1, sa.trans h2, sb.trans h3, wg', wa', wb'⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.WT_ite] at w
    rw [L.ev_ite] at e ⊢
    exact pite_mono (hg.ev w.2.2.2.1 ρ) (ha.ev w.2.2.2.2.1 ρ) (hb.ev w.2.2.2.2.2 ρ) v e

/-! ## Commutativity -/

theorem refines_and_comm {a b : S.Term} {t : S.Ty} :
    S.Refines (L.mk (L.andK a b) t) (L.mk (L.andK b a) t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_and] at w
    exact ⟨(L.WT_and _ _ _).2 ⟨w.2.1, w.1, w.2.2.1, w.2.2.2.2, w.2.2.2.1⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.ev_and] at e ⊢; rw [pand_comm]; exact e

theorem refines_or_comm {a b : S.Term} {t : S.Ty} :
    S.Refines (L.mk (L.orK a b) t) (L.mk (L.orK b a) t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_or] at w
    exact ⟨(L.WT_or _ _ _).2 ⟨w.2.1, w.1, w.2.2.1, w.2.2.2.2, w.2.2.2.1⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.ev_or] at e ⊢; rw [por_comm]; exact e

theorem refines_eq_comm {a b : S.Term} {t : S.Ty} :
    S.Refines (L.mk (L.eqK a b) t) (L.mk (L.eqK b a) t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [L.WT_eq] at w
    exact ⟨(L.WT_eq _ _ _).2 ⟨w.1.symm, w.2.1, w.2.2.2, w.2.2.1⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.ev_eq] at e ⊢; rw [peq_comm]; exact e

end Lang

/-! ## The bool module in the model of a language -/

/-- The rule functions, oracles and helpers of the bool module, in the model of
a language: Kanon generates them (`Ops.bool O`) from the rule functions `O` of
the language and its model. -/
structure Ops {S : Sem} (L : Lang S) where
  b_and : S.Term → S.Term → S.Term
  b_or : S.Term → S.Term → S.Term
  b_not : S.Term → S.Term
  b_ite : S.Term → S.Term → S.Term → S.Term
  sem_eq : S.Term → S.Term → S.Term
  tag_le : S.Term → S.Term → Bool
  sort_by_tag : List S.Term → List S.Term
  at_most_one : List S.Term → Bool
  distinct_check_one : S.Term → List S.Term → Option Bool
  distinct_check : List S.Term → Option Bool

/-- What the rules assume of the bool module in the model: the rule functions
refine their specs, sorting permutes, and the equations of the helpers. -/
structure Ops.Sound {S : Sem} {L : Lang S} (B : Ops L) : Prop where
  b_and : ∀ a b, S.Refines (L.mkAnd a b) (B.b_and a b)
  b_or : ∀ a b, S.Refines (L.mkOr a b) (B.b_or a b)
  b_not : ∀ a, S.Refines (L.mkNot a) (B.b_not a)
  b_ite : ∀ g a b, S.Refines (L.mkIte g a b) (B.b_ite g a b)
  sem_eq : ∀ a b, S.Refines (L.mkEq a b) (B.sem_eq a b)
  sort_by_tag : ∀ l, (B.sort_by_tag l).Perm l
  at_most_one : ∀ a b l, B.at_most_one (a :: b :: l) = false
  distinct_check_one_nil : ∀ a, B.distinct_check_one a [] = some true
  distinct_check_one_cons : ∀ a b l, B.distinct_check_one a (b :: l) =
    if decide (a = b) then some false
    else if L.sure_neq a b then B.distinct_check_one a l else none
  distinct_check_nil : B.distinct_check [] = some true
  distinct_check_cons : ∀ a l, B.distinct_check (a :: l) =
    if B.distinct_check_one a l = some true then B.distinct_check l
    else B.distinct_check_one a l

/-! ## Lifting the calls to the rule functions, for `kanon_lift` -/

namespace Lib

variable {S : Sem} {L : Lang S} {B : Ops L}

theorem lift_b_and (hB : B.Sound) {a a' b b' : S.Term} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (L.mkAnd a b) (B.b_and a' b') :=
  Sem.Refines.trans (Lang.refines_and ha hb) (hB.b_and a' b')

theorem lift_b_or (hB : B.Sound) {a a' b b' : S.Term} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (L.mkOr a b) (B.b_or a' b') :=
  Sem.Refines.trans (Lang.refines_or ha hb) (hB.b_or a' b')

theorem lift_b_not (hB : B.Sound) {a a' : S.Term} (ha : S.Refines a a') :
    S.Refines (L.mkNot a) (B.b_not a') :=
  Sem.Refines.trans (Lang.refines_not ha) (hB.b_not a')

theorem lift_sem_eq (hB : B.Sound) {a a' b b' : S.Term} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (L.mkEq a b) (B.sem_eq a' b') :=
  Sem.Refines.trans (Lang.refines_eq ha hb) (hB.sem_eq a' b')

theorem lift_b_ite (hB : B.Sound) {g g' a a' b b' : S.Term} (hg : S.Refines g g')
    (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (L.mkIte g a b) (B.b_ite g' a' b') :=
  Sem.Refines.trans
    (Lang.refines_ite hg ha hb fun w => Sem.ty_refines ha ((L.WT_ite _ _ _ _).1 w).2.2.2.2.1)
    (hB.b_ite g' a' b')

end Lib

end Kanon.BoolMod
