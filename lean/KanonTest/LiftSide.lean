import KanonCore.Proof

/-! `kanon_lift` leaves the hypothesis `L.P a'` of a lifting lemma, a field of a
variable `L` (as over the interface of a module). -/

namespace KanonTest.LiftSide

open Kanon

@[reducible] def sem : Kanon.Sem where
  Term := Nat
  Ty := Unit
  Val := Nat
  Env := Unit
  ty _ := ()
  WT _ := True
  ev _ t := some t

structure Iface where
  P : Nat → Prop

structure Ops where
  f : Nat → Nat

structure Ops.Sound (L : Iface) (O : Ops) : Prop where
  f : ∀ a, L.P a → sem.Refines a (O.f a)

theorem Lib.lift_f {L : Iface} {O : Ops} (hO : O.Sound L) {a a' : Nat}
    (h : sem.Refines a a') (hp : L.P a') : sem.Refines a (O.f a') :=
  Sem.Refines.trans h (hO.f a' hp)

example : ∀ (L : Iface) (O : Ops) (_ : O.Sound L) (a : Nat), L.P a →
    sem.Refines a (O.f a) := by
  intro L O hO a hp
  kanon_lift
  exact hp

end KanonTest.LiftSide
