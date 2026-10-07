import KanonCore.Proof

/-! `kanon_lift_body` under a goal that `split` tagged (`isTrue`). -/

namespace KanonTest.LiftBody

open Kanon

@[reducible] def sem : Kanon.Sem where
  Term := Nat
  Ty := Unit
  Val := Nat
  Env := Unit
  ty _ := ()
  WT _ := True
  ev _ t := some t
  size _ := 0

structure Ops where
  f : Nat → Nat

structure Ops.Sound (O : Ops) : Prop where
  f : ∀ a, sem.Refines a (O.f a)

theorem Lib.lift_f {O : Ops} (hO : O.Sound) {a a' : Nat} (h : sem.Refines a a') :
    sem.Refines a (O.f a') :=
  Sem.Refines.trans h (hO.f a')

example (O : Ops) (hO : O.Sound) (c : Bool) (a : Nat) :
    sem.Refines a (if c then O.f a else a) := by
  split
  · kanon_lift_body
    exact Sem.Refines.refl
  · exact Sem.Refines.refl

end KanonTest.LiftBody
