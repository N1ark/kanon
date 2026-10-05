import DivisionExample.Statements.Int.div

/-!
# The arm `a / a = 1` of `Int.div`, by a tactic of the function

The subsort `TNonzero` (its Lean predicate is `Nonzero`, in `Semantics.lean`)
asks for it: the arm `a / a = 1` assumes that its divisor is not zero (the
quotient by zero is zero), which `kanon_auto` does not use: a tactic given to the
function `Int.div` (`kanon_tactic`), which its arms try first, proves it. The generated
`Soundness/Int/div.lean` imports this file.
-/

namespace DivisionExample

open Kanon

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

end DivisionExample
