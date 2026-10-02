import KanonCore.BoolMod
import IntsExample.Semantics

/-!
# The language, for the bool module

Kanon's library proves the rules of the bool module once (`Kanon.BoolMod`), for
any language that gives the terms of its nodes, its booleans and the helper
`sure_neq`, with their laws: a `BoolMod.Lang` of its semantics, `boolLang`.
The laws are mostly unfoldings of `Term.WT` and `ev`; the two that need a proof
are that well-typed booleans evaluate to booleans (from `ev_ty`) and that the
terms that `sure_neq` tells apart, which the int module extends with integer
literals, have different values (`sure_neq_sound`).
-/

namespace IntsExample

open Classical Kanon BoolMod

theorem WTList_iff {e : Ty} : ∀ {l : List Term}, Term.WTList e l ↔ ∀ t ∈ l, t.ty = e ∧ t.WT
  | [] => by simp [Term.WTList]
  | t :: ts => by simp [Term.WTList, WTList_iff (l := ts), and_assoc]

theorem evList_eq (ρ : Env) : ∀ l, evList ρ l = l.mapM (ev ρ)
  | [] => rfl
  | t :: ts => by
    rw [evList, List.mapM_cons, evList_eq ρ ts]
    cases ev ρ t <;> cases ts.mapM (ev ρ) <;> rfl

/-- Well-typed terms evaluate to values of their type. -/
theorem ev_ty (ρ : Env) : ∀ (t : Term) (v : Val), t.WT → ev ρ t = some v → v.ty = t.ty
  | .mk (.Var x) t, v, _, e => by
    simp only [ev] at e
    split at e
    · split at e
      · cases e; assumption
      · cases e
    · cases e
  | .mk (.Bool _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.ty]
  | .mk (.Int _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.ty]
  | .mk (.Op1 op a) t, v, w, e => by
    cases op
    simp only [ev, evOp1, Term.WT, Op1.WT] at w e
    rw [pnot_eq_some] at e
    rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Val.ty, w.1.2]
  | .mk (.Op2 op a b) t, v, w, e => by
    cases op <;> simp only [ev, evOp2, Term.WT, Op2.WT] at w e
    · rw [pand_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Val.ty, w.1.2.2]
    · rw [por_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Val.ty, w.1.2.2]
    · rw [peq_eq_some] at e
      obtain ⟨-, -, -, -, rfl⟩ := e
      simp [Val.ty, w.1.2]
    · unfold addV at e
      split at e
      · cases e; simp [Val.ty, w.1.2.2]
      · cases e
    · unfold ltV at e
      split at e
      · cases e; simp [Val.ty, w.1.2.2]
      · cases e
  | .mk (.Op3 op g a b) t, v, w, e => by
    cases op
    simp only [ev, evOp3, Term.WT, Op3.WT] at w e
    obtain ⟨⟨-, hb, rfl⟩, -, wa, wb⟩ := w
    rw [pite_eq_some] at e
    rcases e with ⟨-, e⟩ | ⟨-, -, e⟩
    · exact ev_ty ρ a v wa e
    · rw [ev_ty ρ b v wb e]; exact hb
  | .mk (.OpN op l) t, v, w, e => by
    cases op
    simp only [ev, evOpN, Term.WT, OpN.WT] at w e
    obtain ⟨_, rfl, -⟩ := w
    unfold pdistinct at e
    rw [Option.map_eq_some_iff] at e
    obtain ⟨_, -, rfl⟩ := e
    rfl

/-- The terms that `sure_neq` tells apart: terms of different types, and
different literals. -/
theorem sure_neq_cases {a b : Term} (h : sure_neq a b = true) :
    a.ty ≠ b.ty ∨
      (∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y) ∨
      (∃ x y t t', a = .mk (.Int x) t ∧ b = .mk (.Int y) t' ∧ x ≠ y) := by
  by_cases hty : a.ty = b.ty
  · right
    rcases a with ⟨ka, ta⟩; rcases b with ⟨kb, tb⟩
    simp only [Term.ty_mk] at hty; subst hty
    cases ka <;> cases kb <;> simp_all [sure_neq, ty, firstSome]
  · exact .inl hty

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
  vbool := .bool
  sure_neq := sure_neq
  ty_mk _ _ := rfl
  WT_lit _ _ := by simp [Term.WT]
  WT_not _ _ := by simp [Term.WT, Op1.WT, and_assoc]
  WT_and _ _ _ := by simp [Term.WT, Op2.WT, and_assoc]
  WT_or _ _ _ := by simp [Term.WT, Op2.WT, and_assoc]
  WT_eq _ _ _ := by simp only [Term.WT, Op2.WT]; grind
  WT_ite _ _ _ _ := by simp only [Term.WT, Op3.WT]; grind
  WT_distinct _ _ := by simp [Term.WT, OpN.WT, WTList_iff]
  ev_lit _ _ _ := rfl
  ev_not _ _ _ := by simp [ev, evOp1]
  ev_and _ _ _ _ := by simp [ev, evOp2]
  ev_or _ _ _ _ := by simp [ev, evOp2]
  ev_eq _ _ _ _ := by simp [ev, evOp2]
  ev_ite _ _ _ _ _ := by simp [ev, evOp3]
  ev_distinct ρ l _ := by simp [ev, evOpN, evList_eq]
  ev_bool ρ t v w h e := by
    have := ev_ty ρ t v w e
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | int _ => simp_all [Val.ty]
  vbool_inj _ _ h := by cases h; rfl
  sure_neq_sound ρ a b u h hty _ _ ea eb := by
    rcases sure_neq_cases h with h | ⟨x, y, t, t', rfl, rfl, hxy⟩ | ⟨x, y, t, t', rfl, rfl, hxy⟩
    · exact h hty
    · simp only [ev, Option.some.injEq] at ea eb
      exact hxy (by cases ea.trans eb.symm; rfl)
    · simp only [ev, Option.some.injEq] at ea eb
      exact hxy (by cases ea.trans eb.symm; rfl)

end IntsExample
