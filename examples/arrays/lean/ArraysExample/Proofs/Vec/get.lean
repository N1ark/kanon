import ArraysExample.Statements.Vec.get
import ArraysExample.Lib.Rule

/-!
# The arm `Set (_, j, x)[j] = x` of `Vec.get`, by hand

Reading the element that was just set gives it back: when the read is not
poison, the write was in bounds (`setV`), and `arrayGet_arraySet_same` of
Kanon's library gives the element. The generated `Soundness/Vec/get.lean`
imports this file.
-/

namespace ArraysExample

open Kanon

@[kanon_arm] theorem get_set_same : Vec.get.r_set_same.main.Stmt := by
  intro O hO i u j x t h
  simp only [decide_eq_true_eq] at h
  subst h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · simp only [sem, Vec.get.spec, Term.WT, Op2.WT, Op3.WT, Term.ty_mk] at w ⊢
    exact ⟨w.2.1.2.2.2, w.2.1.1.2.2.1⟩
  · simp only [sem, Vec.get.spec, ev, evOp2, evOp3] at e ⊢
    rcases hw : ev ρ u with _ | (_ | a) <;>
      rcases hj : ev ρ j with _ | (k | _) <;>
      rcases hx : ev ρ x with _ | (y | _) <;>
      simp only [hw, hj, hx, setV, getV] at e <;>
      (try cases e)
    by_cases hin : inBounds a k
    · simp only [hin, ite_true] at e
      have hin' : inBounds (arraySet a k y) k := by
        unfold inBounds at *; rw [arrayLength_arraySet]; exact hin
      simp only [hin', ite_true, Option.some.injEq] at e
      rw [← e, arrayGet_arraySet_same a k y hin]
    · simp [hin] at e

end ArraysExample
