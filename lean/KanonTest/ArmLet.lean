import KanonCore.Proof

/-! `kanon_arm` on a rule function whose rules come after a `let` (the variables
of the sorts of its annotated operands), with a single alternative: the match
is behind the `let`. -/

namespace KanonTest.ArmLet

open Kanon

def f (a : Option Nat) : Option Nat :=
  let n := 1
  (match a with
    | some x => whenSome true (x + n)
    | _ => none)

example (a : Option Nat) (res : Nat) (Q : Nat → Prop) (h : f a = some res)
    (p : ∀ x, Q (x + 1)) : Q res := by
  unfold f at h
  kanon_arm h p

end KanonTest.ArmLet
