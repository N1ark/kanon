import KanonCore.Proof

/-! `kanon_refl` unfolds the heads of the refined terms when they differ:
definitions (a spec that is a helper of the model). -/

namespace KanonTest.Refl

open Kanon

@[reducible] def sem : Kanon.Sem where
  Term := List Nat
  Ty := Unit
  Val := List Nat
  Env := Unit
  ty _ := ()
  WT _ := True
  ev _ t := some t
  size _ := 0

/-- A helper, which is not reducible. -/
def twice (x : List Nat) : List Nat := x ++ x

example (x : List Nat) : sem.Refines (twice x) (x ++ x) := by kanon_refl

example (x : List Nat) : sem.Refines (twice x) (x ++ [0]) ∨ True := by
  fail_if_success (left; kanon_refl)
  exact .inr trivial

end KanonTest.Refl
