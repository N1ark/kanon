import KanonCore.BoolMod
import BoolExample.Semantics
import BoolExample.Model.Bool.sure_neq

/-!
# The language, for the bool module

Kanon's library proves the rules of the bool module once (`Kanon.BoolMod`), for
any language that gives the terms of its nodes, its booleans and the helper
`Bool.sure_neq`, with their laws: a `BoolMod.Lang` of its semantics, `boolLang`.
Here, the terms are variables and the nodes of the module, and the values are
booleans.
-/

namespace BoolExample

open Classical Kanon BoolMod

/-- The language has a single type. -/
theorem Ty.eq_all (a b : Ty) : a = b := by cases a; cases b; rfl

theorem WTList_iff {e : Ty} : ∀ {l : List Term}, Term.WTList e l ↔ ∀ t ∈ l, t.ty = e ∧ t.WT
  | [] => by simp [Term.WTList]
  | t :: ts => by simp [Term.WTList, WTList_iff (l := ts)]

theorem evList_eq (ρ : Env) : ∀ l, evList ρ l = l.mapM (ev ρ)
  | [] => rfl
  | t :: ts => by
    rw [evList, List.mapM_cons, evList_eq ρ ts]
    cases ev ρ t <;> cases ts.mapM (ev ρ) <;> rfl

theorem sure_neq_iff {a b : Term} :
    Bool.sure_neq a b = true ↔
      ∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y := by
  rcases a with ⟨ka, ta⟩; rcases b with ⟨kb, tb⟩
  cases ka <;> cases kb <;> simp [Bool.sure_neq, ty, firstSome]

/-- The language, for the bool module. -/
noncomputable def boolLang : BoolMod.Lang sem where
  Kind := Kind
  mk := Term.mk
  tbool := .TBool
  litK := .Bool
  notK a := .Op1 .Not a
  andK a b := .Op2 .And a b
  orK a b := .Op2 .Or a b
  eqK a b := .Op2 .Eq a b
  iteK g a b := .Op3 .Ite g a b
  distinctK l := .OpN .Distinct l
  vbool := id
  sure_neq := Bool.sure_neq
  ty_mk _ _ := rfl
  WT_lit _ _ := by simp [Term.WT]
  WT_not _ _ := by simp [Term.WT, Op1.WT]
  WT_and _ _ _ := by simp [Term.WT, Op2.WT]
  WT_or _ _ _ := by simp [Term.WT, Op2.WT]
  WT_eq _ _ _ := by simp [Term.WT, Op2.WT]
  WT_ite _ _ _ _ := by simp [Term.WT, Op3.WT]
  WT_distinct _ _ := by simp [Term.WT, OpN.WT, WTList_iff]
  ev_lit _ _ _ := rfl
  ev_not _ _ _ := by simp [ev, evOp1]
  ev_and _ _ _ _ := by simp [ev, evOp2]
  ev_or _ _ _ _ := by simp [ev, evOp2]
  ev_eq _ _ _ _ := by simp [ev, evOp2]
  ev_ite _ _ _ _ _ := by simp [ev, evOp3]
  ev_distinct ρ l _ := by simp [ev, evOpN, evList_eq]
  ev_bool _ _ v _ _ _ := ⟨v, rfl⟩
  vbool_inj _ _ h := h
  sure_neq_sound ρ a b u h _ _ _ ea eb := by
    obtain ⟨x, y, t, t', rfl, rfl, hxy⟩ := sure_neq_iff.1 h
    simp only [ev, Option.some.injEq] at ea eb
    exact hxy (ea.trans eb.symm)

end BoolExample
