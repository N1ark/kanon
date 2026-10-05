import Exp.L2.Lang
import KanonCore.Proof

/-! The per-language glue that Kanon generates whatever the option: the
inversion of the closed matches of the rule functions (a result of a rule is an
instance of one of its arms) and the soundness of the step functions, from the
statements of the arms. Also the global laws (proved by induction over ALL the
nodes of the language). -/

set_option linter.unusedVariables false

noncomputable section

namespace Exp.L2

open Classical Kanon

@[simp] theorem Val.toBool_eq_some {v : Val} {b : Bool} : v.toBool = some b ↔ v = .bool b := by
  cases v <;> simp [Val.toBool]
@[simp] theorem Val.toInt_eq_some {v : Val} {z : Int} : v.toInt = some z ↔ v = .int z := by
  cases v <;> simp [Val.toInt]
@[simp] theorem Term.ty_mk {k : Kind} {t : Ty} : (Term.mk k t).ty = t := rfl

theorem ev_cases (ρ : Env) (t : Term) :
    ev ρ t = none ∨ (∃ b, ev ρ t = some (.bool b)) ∨ ∃ z, ev ρ t = some (.int z) := by
  rcases ev ρ t with _ | _ | _ <;> simp

elab "l2_cases" : tactic => Kanon.Proof.caseAllAtoms (some #[``ev_cases])

/-- `Sem.Refines.intro` at the types of the language. -/
theorem Refines.intro' {a b : Term} (syn : a.WT → b.WT ∧ b.ty = a.ty)
    (sem : ∀ (ρ : Env) (v : Val), a.WT → b.WT → ev ρ a = some v → ev ρ b = some v) :
    Refines a b := Sem.Refines.intro syn sem

/-- Inverts a rule function: `r O args = some res` gives the arm. -/
macro "inv" h:ident : tactic => `(tactic| (
  (repeat' split at $h:ident) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at $h:ident) <;> (try subst $h:ident)))

theorem B.not_.step_sound (h1 : B.not_.lit.Stmt) (h2 : B.not_.nn.Stmt) (h3 : B.not_.lt.Stmt)
    (h4 : B.not_.default.Stmt) (O : Ops) (hO : O.Sound) (v : Term) :
    Refines (B.not_.spec v) (B.not_.step O v) := by
  unfold B.not_.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.not_.r_lit at h; inv h; · exact h1 O hO _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.not_.r_nn at h; inv h; · exact h2 O hO _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.not_.r_lt at h; inv h; · exact h3 O hO _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.not_.r_default at h; cases h; exact h4 O hO _
  exact Refinement.firstSome_nil

theorem B.ite.step_sound (h1 : B.ite.true_.Stmt) (h2 : B.ite.same.Stmt) (h3 : B.ite.bool.Stmt)
    (h4 : B.ite.default.Stmt) (O : Ops) (hO : O.Sound) (g a b : Term) :
    Refines (B.ite.spec g a b) (B.ite.step O g a b) := by
  unfold B.ite.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.ite.r_true at h; inv h; · exact h1 O hO _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.ite.r_same at h; inv h; · exact h2 O hO _ _ _ ‹_›
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.ite.r_bool at h; inv h; · exact h3 O hO _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.ite.r_default at h; cases h; exact h4 O hO _ _ _
  exact Refinement.firstSome_nil

theorem B.eq.step_sound (h0 : B.eq.ints.Stmt) (h1 : B.eq.same.Stmt) (h2 : B.eq.neq.Stmt)
    (h3 : B.eq.lits.Stmt) (h4 : B.eq.default.Stmt) (O : Ops) (hO : O.Sound) (a b : Term) :
    Refines (B.eq.spec a b) (B.eq.step O a b) := by
  unfold B.eq.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.eq.r_ints at h; inv h; · exact h0 O hO _ _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.eq.r_same at h; inv h; · exact h1 O hO _ _ ‹_›
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.eq.r_neq at h; inv h; · exact h2 O hO _ _ ‹_›
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.eq.r_lits at h; inv h; · exact h3 O hO _ _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold B.eq.r_default at h; cases h; exact h4 O hO _ _
  exact Refinement.firstSome_nil

theorem I.add.step_sound (h1 : I.add.lits.Stmt) (h2 : I.add.zero.Stmt) (h3 : I.add.ite.Stmt)
    (h35 : I.add.negself.Stmt) (h4 : I.add.default.Stmt) (O : Ops) (hO : O.Sound) (a b : Term) :
    Refines (I.add.spec a b) (I.add.step O a b) := by
  unfold I.add.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.add.r_lits at h; inv h; · exact h1 O hO _ _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.add.r_zero at h; inv h; · exact h2 O hO _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.add.r_ite at h; inv h; · exact h3 O hO _ _ _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.add.r_negself at h; inv h; · exact h35 O hO _ _ _ ‹_›
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.add.r_default at h; cases h; exact h4 O hO _ _
  exact Refinement.firstSome_nil

theorem I.lt.step_sound (h1 : I.lt.lits.Stmt) (h2 : I.lt.same.Stmt) (h3 : I.lt.ofbool.Stmt)
    (h4 : I.lt.default.Stmt) (O : Ops) (hO : O.Sound) (a b : Term) :
    Refines (I.lt.spec a b) (I.lt.step O a b) := by
  unfold I.lt.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.lt.r_lits at h; inv h; · exact h1 O hO _ _ _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.lt.r_same at h; inv h; · exact h2 O hO _ _ ‹_›
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.lt.r_ofbool at h; inv h; · exact h3 O hO _ _ _ _ ‹_›
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.lt.r_default at h; cases h; exact h4 O hO _ _
  exact Refinement.firstSome_nil

theorem I.of_bool.step_sound (h1 : I.of_bool.true_.Stmt) (h2 : I.of_bool.false_.Stmt)
    (h3 : I.of_bool.default.Stmt) (O : Ops) (hO : O.Sound) (a : Term) :
    Refines (I.of_bool.spec a) (I.of_bool.step O a) := by
  unfold I.of_bool.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.of_bool.r_true at h; inv h; · exact h1 O hO _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.of_bool.r_false at h; inv h; · exact h2 O hO _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold I.of_bool.r_default at h; cases h; exact h3 O hO _
  exact Refinement.firstSome_nil

theorem X.neg.step_sound (h1 : X.neg.lit.Stmt) (h2 : X.neg.nn.Stmt)
    (h3 : X.neg.default.Stmt) (O : Ops) (hO : O.Sound) (a : Term) :
    Refines (X.neg.spec a) (X.neg.step O a) := by
  unfold X.neg.step
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold X.neg.r_lit at h; inv h; · exact h1 O hO _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold X.neg.r_nn at h; inv h; · exact h2 O hO _ _
    all_goals cases h
  refine Refinement.firstSome_cons (fun r h => ?_) ?_
  · unfold X.neg.r_default at h; cases h; exact h3 O hO _
  exact Refinement.firstSome_nil

/-! ## Global laws (whole-language inductions) -/

theorem pite_eq_some {V : Type} {db : V → Option Bool} {g a b : Option V} {v : V}
    (h : pite db g a b = some v) : a = some v ∨ b = some v := by
  simp only [pite, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, c, _, h⟩ := h
  cases c <;> simp_all

/-- Well-typed terms evaluate to values of their type. -/
theorem ev_ty (ρ : Env) : ∀ (t : Term) (v : Val), t.WT → ev ρ t = some v → v.ty = t.ty
  | .mk (.Var x) t, v, _, e => by
    simp only [ev] at e; split at e <;> simp_all [Term.ty]
  | .mk (.BIte g a b) t, v, w, e => by
    simp only [ev, Term.WT] at w e
    rcases pite_eq_some e with e | e
    · rw [ev_ty ρ a v w.2.2.2.2.1 e]; exact w.2.1
    · rw [ev_ty ρ b v w.2.2.2.2.2 e]; exact w.2.2.1
  | .mk (.BLit _) t, v, w, e | .mk (.BNot _) t, v, w, e | .mk (.BEq _ _) t, v, w, e
  | .mk (.ILit _) t, v, w, e | .mk (.Add _ _) t, v, w, e | .mk (.Lt _ _) t, v, w, e
  | .mk (.OfBool _) t, v, w, e | .mk (.Neg _) t, v, w, e => by
    simp only [ev, Term.WT, pnot, peq, padd, plt, pofbool, pneg, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq] at w e
    grind [Val.ty, Term.ty]

theorem ev_bool (ρ : Env) (t : Term) (v : Val) (w : t.WT) (h : t.ty = .TBool)
    (e : ev ρ t = some v) : ∃ b, v.toBool = some b := by
  have := ev_ty ρ t v w e
  cases v <;> simp_all [Val.ty, Val.toBool]

/-- Inversion of the extensible helper: its cases, by module. -/
theorem B.sure_neq_cases {a b : Term} (h : B.sure_neq a b = true) :
    (∃ x y t t', a = .mk (.BLit x) t ∧ b = .mk (.BLit y) t' ∧ x ≠ y) ∨
      (∃ x y t t', a = .mk (.ILit x) t ∧ b = .mk (.ILit y) t' ∧ x ≠ y) := by
  unfold B.sure_neq at h
  unfold B.sure_neq.c_bool I.sure_neq.c_int at h
  split at h
  · simp_all [firstSome]
  · split at h <;> simp_all [firstSome]

end Exp.L2
