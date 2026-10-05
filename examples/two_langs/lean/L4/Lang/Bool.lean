import L4.Interface.Bool
import L4.Model.Bool.sure_neq

/-!
# The language, for the bool module

The language gives the instances of the `Sem` classes of its modules in a
file per module (`Lang/Bool.lean`, `Lang/Cfg.lean`, `Lang/Word.lean`), which the
proofs over the interface of a module import with those of the modules it
uses: a change to the interface of the word module does not rebuild the proofs
that only need the bool module (the commutativity of `And`, say).
-/

namespace L4

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
  | .mk (.Wd _ _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.HasTy]
  | .mk (.WBlob _ _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.HasTy]
  | .mk (.WFit _) t, v, w, e => by
    simp only [ev, Option.some.injEq] at e; subst e
    simp_all [Term.WT, Val.HasTy]
  | .mk (.Op1 op a) t, v, w, e => by
    cases op <;> simp only [ev, evOp1, Term.WT, Op1.WT] at w e
    · rw [pnot_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Val.HasTy, w.1.2]
    · have := ev_ty ρ a v w.2 e
      rwa [w.1.1, ← w.1.2] at this
    · obtain ⟨⟨n, hn, -, rfl⟩, wa⟩ := w
      have := ev_ty ρ a v wa e
      rw [hn] at this
      cases v <;> simp_all [Val.HasTy]
  | .mk (.Op2 op a b) t, v, w, e => by
    cases op <;> simp only [ev, evOp2, Term.WT, Op2.WT] at w e
    · rw [pand_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Val.HasTy, w.1.2.2]
    · rw [por_eq_some] at e
      rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Val.HasTy, w.1.2.2]
    · rw [peq_eq_some] at e
      obtain ⟨-, -, -, -, rfl⟩ := e
      simp [Val.HasTy, w.1.2]
    · simp only [WordMod.addV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
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
    a.ty ≠ b.ty ∨ (∃ x y t t', a = .mk (.Bool x) t ∧ b = .mk (.Bool y) t' ∧ x ≠ y) := by
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
    rcases sure_neq_cases h with h | ⟨x, y, t, t', rfl, rfl, hxy⟩
    · exact h hty
    · simp only [ev, Option.some.injEq] at ea eb
      exact hxy (by cases ea.trans eb.symm; rfl)

end L4
