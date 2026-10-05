import MixMod.Sem
import L3.Interface
import L3.Model.Bool.sure_neq

/-!
# The language, for its modules

The bool, num, neg, even and mix modules are proved once (`KanonBool`, `NumMod`, `NegMod`,
`EvenMod`, `MixMod`): the language
gives their interfaces (`boolSyntax`, …, generated in `Interface.lean`) and what
they need of its semantics (the instances of their `Sem` classes): its values, the evaluation of the nodes (by
definition, and `evList_eq`), and the two laws that need an induction or a case
analysis on its terms.
-/

namespace L3

open Classical Kanon KanonBool

@[kanon_law] theorem evList_eq (ρ : Env) : ∀ l, evList ρ l = l.mapM (ev ρ)
  | [] => rfl
  | t :: ts => by
    rw [evList, List.mapM_cons, evList_eq ρ ts]
    cases ev ρ t <;> cases ts.mapM (ev ρ) <;> rfl

/-- Well-typed terms evaluate to values of their type. -/
theorem ev_ty (ρ : Env) : ∀ (t : Term) (v : Val), t.WT → ev ρ t = some v → v.HasTy t.ty
  | .mk (.Var x) t, v, _, e => by
    simp only [ev] at e
    split at e
    · split at e
      · cases e; assumption
      · cases e
    · cases e
  | .mk (.Bool _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.HasTy]
  | .mk (.Num _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.HasTy]
  | .mk (.Ev _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.HasTy, even_inv]
  | .mk (.Op1 op a) t, v, w, e => by
    cases op <;> simp only [ev, evOp1, Term.WT, Op1.WT] at w e
    · rw [pnot_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Val.HasTy, w.1.2]
    · simp only [NegMod.negV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
      obtain ⟨-, -, -, -, rfl⟩ := e
      simp [Val.HasTy, w.1.2]
    · simp only [EvenMod.rem2V, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
      obtain ⟨-, -, -, -, rfl⟩ := e
      simp [Val.HasTy, w.1.2]
  | .mk (.Op2 op a b) t, v, w, e => by
    cases op <;> simp only [ev, evOp2, Term.WT, Op2.WT] at w e
    · rw [pand_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Val.HasTy, w.1.2.2]
    · rw [por_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Val.HasTy, w.1.2.2]
    · rw [peq_eq_some] at e
      obtain ⟨-, -, -, -, rfl⟩ := e
      simp [Val.HasTy, w.1.2]
    all_goals
      simp only [NumMod.op2, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
      obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := e
      simp [Val.HasTy, w.1.2.2]
  | .mk (.Op3 op g a b) t, v, w, e => by
    cases op
    simp only [ev, evOp3, Term.WT, Op3.WT] at w e
    obtain ⟨⟨-, hb, rfl⟩, -, wa, wb⟩ := w
    rw [pite_eq_some] at e
    rcases e with ⟨-, e⟩ | ⟨-, -, e⟩
    · exact ev_ty ρ a v wa e
    · have := ev_ty ρ b v wb e
      rwa [hb] at this
  | .mk (.OpN op l) t, v, w, e => by
    cases op
    simp only [ev, evOpN, Term.WT, OpN.WT] at w e
    obtain ⟨_, rfl, -⟩ := w
    unfold pdistinct at e
    rw [Option.map_eq_some_iff] at e
    obtain ⟨_, -, rfl⟩ := e
    rfl

/-- The terms that `Bool.sure_neq` tells apart: terms of different types, and
different literals. -/
theorem sure_neq_cases {a b : Term} (h : Bool.sure_neq a b = true) :
    a.ty ≠ b.ty ∨
      (∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y) ∨
      (∃ x y t t', a = .mk (.Num x) t ∧ b = .mk (.Num y) t' ∧ x ≠ y) := by
  by_cases hty : a.ty = b.ty
  · right
    rcases a with ⟨ka, ta⟩; rcases b with ⟨kb, tb⟩
    simp only [Term.ty_mk] at hty; subst hty
    cases ka <;> cases kb <;> simp_all [Bool.sure_neq, ty, firstSome]
  · exact .inl hty

/-- What the bool module needs of the semantics. -/
noncomputable instance boolSem : KanonBool.Sem (S := sem) boolSyntax where
  vbool := .bool
  ev_bool ρ t v w h e := by
    have := ev_ty ρ t v w e
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | int _ => simp_all [Val.HasTy, boolSyntax]
  sure_neq_sound ρ a b u h hty _ _ ea eb := by
    rcases sure_neq_cases h with h | ⟨x, y, t, t', rfl, rfl, hxy⟩ | ⟨x, y, t, t', rfl, rfl, hxy⟩
    · exact h hty
    · simp only [ev, Option.some.injEq] at ea eb
      exact hxy (by cases ea.trans eb.symm; rfl)
    · simp only [ev, Option.some.injEq] at ea eb
      exact hxy (by cases ea.trans eb.symm; rfl)

/-- What the num module needs of the semantics. -/
noncomputable instance numSem : NumMod.Sem (S := sem) numSyntax where
  vint := .int
  toInt := Val.toInt

/-- What the neg module needs of the semantics: its laws hold by definition. -/
noncomputable instance negSem : NegMod.Sem (S := sem) negSyntax := {}

/-- What the even module needs of the semantics: its laws, and the meaning of
the invariant of `TEven`, hold by definition. -/
noncomputable instance evenSem : EvenMod.Sem (S := sem) evenSyntax := {}

/-- The mix module needs nothing more. -/
instance mixSem : MixMod.Sem (S := sem) mixSyntax := {}

end L3
