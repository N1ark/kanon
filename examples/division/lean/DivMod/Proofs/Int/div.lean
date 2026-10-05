import DivMod.Statements.Int.div
import DivMod.Lib.Rule

/-!
# The arm `a / a = 1` of `Int.div`, by a tactic of the function

The subsort `TNonzero` (its Lean predicate is `Nonzero`, a field of the
interface, whose meaning is `Sem.nonzero`) asks for it: the arm `a / a = 1`
assumes that its divisor is not zero (the quotient by zero is zero), which
`kanon_auto` does not use: a tactic given to the function `Int.div`
(`kanon_tactic`), which its arms try first, proves it. The generated
`Soundness/Int/div.lean` imports this file.
-/

namespace DivMod

open Kanon

/-- `a / a` is refined by `1`, when `a` is not zero (the divisor, `Nonzero`: the
quotient by zero is zero). -/
macro "kanon_div_self" : tactic => `(tactic| (
  intro S _ _ B L _ O hO v1 v2 hs hg
  simp only [decide_eq_true_eq] at hg
  subst hg
  refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · -- typing: `1` is an integer
    simp [Int.div.spec, L.WT_Div, L.WT_Int, B.ty_node] at w ⊢
  · -- values: a non-zero integer divided by itself is 1
    have hw : S.WT v1 := by
      simp only [Int.div.spec, L.WT_Div] at w
      exact w.2.1
    simp only [Int.div.spec, Sem.ev_Div, Sem.ev_Int, divV, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at e ⊢
    obtain ⟨x, hx, y, hy, m, hm, n, hn, e⟩ := e
    rw [hx] at hy; cases hy
    rw [hm] at hn; cases hn
    have hne : m ≠ 0 := Sem.nonzero v1 hs ρ m (by
      rw [Kanon.Sem.eval_eq_ev hw, hx, Sem.vint_toInt x m hm])
    rw [← e, Int.ediv_self hne]))

-- the arms of `Int.div` try `kanon_div_self` before `kanon_auto`
attribute [kanon_tactic "kanon_div_self"] Int.div.spec

end DivMod
