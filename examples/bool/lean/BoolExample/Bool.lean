import KanonCore.BoolMod
import BoolExample.Semantics

/-!
# The language, for the bool module

Kanon's library proves the rules of the bool module once (`Kanon.BoolMod`), for
any language that gives the terms of its nodes, its booleans and its primitives,
with their laws: a `BoolMod.Lang` of its semantics, `boolLang`. Here, the terms
are variables and the nodes of the module, and the values are booleans.
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
    sure_neq a b = true ↔
      ∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y := by
  rcases a with ⟨ka, ta⟩; rcases b with ⟨kb, tb⟩
  cases ka <;> cases kb <;> simp [sure_neq, ty, firstSome]

/-- The language, for the bool module. -/
noncomputable def boolLang : BoolMod.Lang sem where
  Kind := Kind
  mk := Term.mk
  tbool := .TBool
  litK := .Bool
  notK a := .Unop .Not a
  andK a b := .Binop .And a b
  orK a b := .Binop .Or a b
  eqK a b := .Binop .Eq a b
  iteK g a b := .Triop .Ite g a b
  distinctK l := .Nop .Distinct l
  vbool := id
  equal := equal
  sure_neq := sure_neq
  ty_mk _ _ := rfl
  WT_lit _ _ := by simp [Term.WT]
  WT_not _ _ := by simp [Term.WT, Unop.WT]
  WT_and _ _ _ := by simp [Term.WT, Binop.WT]
  WT_or _ _ _ := by simp [Term.WT, Binop.WT]
  WT_eq _ _ _ := by simp [Term.WT, Binop.WT]
  WT_ite _ _ _ _ := by simp [Term.WT, Triop.WT]
  WT_distinct _ _ := by simp [Term.WT, WTList_iff]
  ev_lit _ _ _ := rfl
  ev_not _ _ _ := by simp [ev, evUnop]
  ev_and _ _ _ _ := by simp [ev, evBinop]
  ev_or _ _ _ _ := by simp [ev, evBinop]
  ev_eq _ _ _ _ := by simp [ev, evBinop]
  ev_ite _ _ _ _ _ := by simp [ev, evTriop]
  ev_distinct ρ l _ := by simp [ev, evList_eq]
  ev_bool _ _ v _ _ _ := ⟨v, rfl⟩
  vbool_inj _ _ h := h
  equal_eq _ _ h := by simpa [equal] using h
  sure_neq_sound ρ a b u h _ _ _ ea eb := by
    obtain ⟨x, y, t, t', rfl, rfl, hxy⟩ := sure_neq_iff.1 h
    simp only [ev, Option.some.injEq] at ea eb
    exact hxy (ea.trans eb.symm)

end BoolExample
