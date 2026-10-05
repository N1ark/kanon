import DivisionExample.Lib.Rule

/-!
# Hand-written proofs

`kanon_auto` (`Lib/Rule.lean`) proves the arms of this language that it can. A
proof written by hand replaces `kanon_auto` for the statement it proves
(`@[kanon_arm]`): the first one below, of the commutativity of `+`, shows how.
Its statement, `Op2.Plus.comm.Stmt` (`Statements.lean`), is that `a + b` is
refined by `b + a`, at any type `t`.

The subsort `TNonzero` (its Lean predicate is `Nonzero`, in `Semantics.lean`) asks
two more proofs: the arm `a / a = 1` assumes that its divisor is not zero (the
quotient by zero is zero), which a tactic given to the function `Int.div`
(`kanon_tactic`) proves, and `Int.sq1.post.main.Stmt` says that what `sq1`
returns, which has the sort `TNonzero`, is not zero.
-/

namespace DivisionExample

open Kanon

/-- `a + b` is refined by `b + a`. -/
@[kanon_arm] theorem plus_comm : Op2.Plus.comm.Stmt := by
  intro a b t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · -- typing: `b + a` is well-typed, of the type `t`, when `a + b` is
    simp only [sem, Term.WT, Op2.WT] at w ⊢
    exact ⟨⟨⟨w.1.2.1, w.1.1, w.1.2.2⟩, w.2.2, w.2.1⟩, trivial⟩
  · -- values: the sum of two integers commutes, and is otherwise poison
    simp only [sem, ev, evOp2] at e ⊢
    unfold addV at e ⊢
    split at e
    · next x y ha hb => cases e; rw [ha, hb, Int.add_comm]
    · cases e

/-- `a / a` is refined by `1`, when `a` is not zero (the divisor, `Nonzero`: the
quotient by zero is zero). -/
macro "kanon_div_self" : tactic => `(tactic| (
  intro O hO v1 v2 hs hg
  simp only [decide_eq_true_eq] at hg
  subst hg
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · -- typing: `1` is an integer
    simp [sem, Int.div.spec, Term.WT, Op2.WT] at w ⊢
  · -- values: a non-zero integer divided by itself is 1
    have hw : v1.WT := by
      simp only [Int.div.spec, Term.WT, Op2.WT] at w
      exact w.2.1
    simp only [sem, Int.div.spec, ev, evOp2] at e ⊢
    unfold divV at e
    split at e
    · next x y hx hy =>
      rw [hx] at hy
      have hxy : x = y := by simpa using hy
      subst hxy
      have hne : x ≠ 0 := hs ρ x ((Sem.eval_eq_ev (S := sem) hw).trans hx)
      cases e
      simp [Int.ediv_self hne]
    · cases e))

-- the arms of `Int.div` try `kanon_div_self` before `kanon_auto`
attribute [kanon_tactic "kanon_div_self"] Int.div.spec

/-- What `sq1` returns satisfies `Nonzero`: its rule gives back its spec, whose
value is the square of an integer plus one. -/
@[kanon_arm] theorem sq1_nonzero : Int.sq1.post.main.Stmt := by
  intro O hO v ρ z h
  simp [Int.sq1.step, Int.sq1.r_default, firstSome, whenSome, Int.sq1.spec, Sem.eval, sem, ev, evOp1, sq1V] at h
  obtain ⟨-, h⟩ := h
  split at h
  · next x _ =>
    have hz : z = x * x + 1 := by simpa using h.symm
    have : 0 ≤ x * x := by
      rcases Int.le_total 0 x with h0 | h0
      · exact Int.mul_nonneg h0 h0
      · exact Int.mul_nonneg_of_nonpos_of_nonpos h0 h0
    omega
  · cases h

end DivisionExample
