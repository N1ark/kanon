import KanonCore.Proof

/-! The tactics of refinement fail fast on different terms: they do not
evaluate them (here, their typing) to compare them. -/

namespace KanonTest.Comm

open Kanon

/-- Costly to evaluate: unfolding `slow 3000` exceeds the recursion depth. -/
def slow : Nat → Bool
  | 0 => true
  | n + 1 => slow n

@[reducible] def sem : Kanon.Sem where
  Term := Nat
  Ty := Unit
  Val := Nat
  Env := Unit
  ty _ := ()
  WT t := slow t = true
  ev _ t := some t

example (h : sem.Refines 3000 3001) : sem.Refines 3000 3001 := by
  fail_if_success kanon_refl
  fail_if_success kanon_comm
  exact h

end KanonTest.Comm
