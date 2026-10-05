import DivisionExample.Statements.Int.sq1
import DivisionExample.Lifts

/-!
# The postcondition of `Int.sq1`, by hand

`Int.sq1.post.main.Stmt` says that what `sq1` returns, which has the sort
`TNonzero`, is not zero. The generated `Soundness/Int/sq1.lean` imports this
file.
-/

namespace DivisionExample

open Kanon

/-- What `sq1` returns satisfies `Nonzero`: its rule gives back its spec, whose
value is the square of an integer plus one. -/
@[kanon_arm] theorem sq1_nonzero : Int.sq1.post.main.Stmt := by
  intro O hO v ρ z h
  simp [Int.sq1.step, Int.sq1.r_default, firstSome, whenSome, Int.sq1.spec, Sem.eval, sem, ev, evOp1, DivMod.sq1V, Val.toInt] at h
  obtain ⟨-, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨⟨x⟩, -, h⟩ := h
  have hz : z = x * x + 1 := by simpa using h.symm
  have : 0 ≤ x * x := by
    rcases Int.le_total 0 x with h0 | h0
    · exact Int.mul_nonneg h0 h0
    · exact Int.mul_nonneg_of_nonpos_of_nonpos h0 h0
  omega

/-- Lifting a call of `div` leaves the predicate of its divisor (here, by `kanon_lift`, on
terms that a rule could build: `sq1 (v1 / v2)`), for the proof of the rule. -/
example (O : Ops) (hO : O.Sound) (v1 v2 : Term) (hs : Nonzero v2) :
    Refines (Int.sq1.spec (Int.div.spec v1 v2)) (O.int_sq1 (O.int_div v1 v2)) := by
  kanon_lift
  exact hs

end DivisionExample
