import KanonCore.Generic
import DivMod.Syntax

/-!
# What the int module needs of the semantics of a language

The rules of the int module (`../int.kn`) are proved once (`DivMod`), for every
language that uses it, over its interface `L : DivMod.Syntax S` (generated, in
`Syntax.lean`) and what the proofs need of the semantics `S`, `DivMod.Sem L`:

- the integers among its values (`vint`), and how to read them back (`toInt`);
- the evaluation of its nodes, by the operations below, which the language uses
  in its own evaluation (so that these laws hold by definition: `kanon_law`);
- the meaning of the subsort `TNonzero`, whose Lean predicate `Nonzero` is a
  field of the interface: a term that satisfies it has no value zero.
-/

namespace DivMod

open Classical Kanon
open Kanon.Sem (OLe)

section
variable {V : Type} (vint : Int → V) (toInt : V → Option Int)

/-- The sum of two integers; poison otherwise. -/
def addV (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (toInt x).bind fun m => (toInt y).map fun n => vint (m + n)

/-- The quotient of two integers, which is zero if the divisor is; poison
otherwise. -/
def divV (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (toInt x).bind fun m => (toInt y).map fun n => vint (m / n)

/-- The square of an integer, plus one; poison otherwise. -/
def sq1V (a : Option V) : Option V :=
  a.bind fun x => (toInt x).map fun m => vint (m * m + 1)

variable {vint toInt}

theorem addV_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (addV vint toInt a b) (addV vint toInt a' b') := by
  intro v e
  simp only [addV, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, y, hy, rest⟩ := e
  exact ⟨x, ha _ hx, y, hb _ hy, rest⟩

theorem divV_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (divV vint toInt a b) (divV vint toInt a' b') := by
  intro v e
  simp only [divV, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, y, hy, rest⟩ := e
  exact ⟨x, ha _ hx, y, hb _ hy, rest⟩

theorem sq1V_mono {a a' : Option V} (ha : OLe a a') :
    OLe (sq1V vint toInt a) (sq1V vint toInt a') := by
  intro v e
  simp only [sq1V, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, rest⟩ := e
  exact ⟨x, ha _ hx, rest⟩

theorem addV_comm (a b : Option V) : addV vint toInt a b = addV vint toInt b a := by
  cases a <;> cases b <;> simp only [addV, Option.bind_none, Option.bind_some] <;>
    (try rfl) <;> rename_i x y <;> cases toInt x <;> cases toInt y <;>
    simp [Int.add_comm]

end

/-- What the int module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} (L : Syntax B) where
  /-- The integer values. -/
  vint : Int → S.Val
  /-- The integer of a value, if it is one. -/
  toInt : S.Val → Option Int
  toInt_vint : ∀ z, toInt (vint z) = some z := by intros; rfl
  vint_toInt : ∀ v z, toInt v = some z → v = vint z := by
    intro v z h; cases v <;> cases h <;> rfl
  ev_Int : ∀ ρ z t, S.ev ρ (B.node (L.IntK z) t) = some (vint z) := by kanon_law
  ev_Plus : ∀ ρ a b t, S.ev ρ (B.node (L.PlusK a b) t) =
    addV vint toInt (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Div : ∀ ρ a b t, S.ev ρ (B.node (L.DivK a b) t) =
    divV vint toInt (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Sq1 : ∀ ρ a t, S.ev ρ (B.node (L.Sq1K a) t) = sq1V vint toInt (S.ev ρ a) := by kanon_law
  /-- The terms of the subsort `TNonzero` have no value zero. -/
  nonzero : ∀ t, L.Nonzero t → ∀ ρ z, S.eval ρ t = some (vint z) → z ≠ 0 := by
    intro t h; exact h

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} {L : Syntax B} [Sem L]

/-- Different integers are different values. -/
theorem vint_eq_iff {a b : Int} : vint L a = vint L b ↔ a = b :=
  ⟨fun h => by simpa [toInt_vint] using congrArg (toInt L) h, fun h => h ▸ rfl⟩

/-- The values of a value as an integer. -/
theorem toInt_cases {u : S.Val} : toInt L u = none ∨ ∃ z, toInt L u = some z ∧ u = vint L z := by
  rcases h : toInt L u with _ | z
  · exact .inl rfl
  · exact .inr ⟨z, rfl, vint_toInt u z h⟩

end Sem

/-- The values of any term. -/
theorem Sem.ev_opt {S : Kanon.Sem} {ρ : S.Env} {t : S.Term} :
    S.ev ρ t = none ∨ ∃ v, S.ev ρ t = some v := by
  cases S.ev ρ t <;> simp

end DivMod
