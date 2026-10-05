import KanonBool.Sem
import IntMod.Syntax

/-!
# What the int module needs of the semantics of a language

The rules of the int module (`../int.kn`) are proved once (`IntMod`), for every
language that uses it, over its interface `L : IntMod.Syntax S` (generated, in
`Syntax.lean`) and what the proofs need of the semantics `S`, `IntMod.Sem L`
(which extends what the bool module needs, `KanonBool.Sem`):

- the integers among its values (`vint`), and how to read them back (`toInt`);
- the evaluation of its nodes, by the operations below, which the language uses
  in its own evaluation (so that these laws hold by definition: `kanon_law`).

The operations are those of a language whose values `V` have integers and
booleans: `addV` and `ltV` are poison when an operand is, or is not an integer.
-/

namespace IntMod

open Classical Kanon KanonBool
open Kanon.Sem (OLe)

section
variable {V : Type} (vint : Int → V) (toInt : V → Option Int) (vbool : Bool → V)

/-- The sum of two integers; poison otherwise. -/
def addV (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (toInt x).bind fun m => (toInt y).map fun n => vint (m + n)

/-- The order of two integers; poison otherwise. -/
def ltV (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (toInt x).bind fun m => (toInt y).map fun n => vbool (decide (m < n))

variable {vint toInt vbool}

theorem addV_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (addV vint toInt a b) (addV vint toInt a' b') := by
  intro v e
  simp only [addV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
  obtain ⟨x, hx, y, hy, rest⟩ := e
  exact ⟨x, ha _ hx, y, hb _ hy, rest⟩

theorem ltV_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (ltV toInt vbool a b) (ltV toInt vbool a' b') := by
  intro v e
  simp only [ltV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
  obtain ⟨x, hx, y, hy, rest⟩ := e
  exact ⟨x, ha _ hx, y, hb _ hy, rest⟩

theorem addV_comm (a b : Option V) : addV vint toInt a b = addV vint toInt b a := by
  cases a <;> cases b <;> simp only [addV, Option.bind_none, Option.bind_some] <;>
    (try rfl) <;> rename_i x y <;> cases toInt x <;> cases toInt y <;>
    simp [Int.add_comm]

end

/-- What the int module needs of the semantics `S` of a language, for its
interface `L`. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] (L : Syntax S) extends
    toBoolSem : KanonBool.Sem L.toBoolSyntax where
  /-- The integer values. -/
  vint : Int → S.Val
  /-- The integer of a value, if it is one. -/
  toInt : S.Val → Option Int
  toInt_vint : ∀ z, toInt (vint z) = some z := by intros; rfl
  vint_toInt : ∀ v z, toInt v = some z → v = vint z := by
    intro v z h; cases v <;> cases h <;> rfl
  ev_Int : ∀ ρ z t, S.ev ρ (L.node (L.IntK z) t) = some (vint z) := by kanon_law
  ev_Plus : ∀ ρ a b t, S.ev ρ (L.node (L.PlusK a b) t) =
    addV vint toInt (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Lt : ∀ ρ a b t, S.ev ρ (L.node (L.LtK a b) t) =
    ltV toInt vbool (S.ev ρ a) (S.ev ρ b) := by kanon_law

/-- Different integers are different values. -/
theorem Sem.vint_eq_iff {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {L : Syntax S}
    [Sem L] {a b : Int} : Sem.vint L a = Sem.vint L b ↔ a = b :=
  ⟨fun h => by simpa [Sem.toInt_vint] using congrArg (Sem.toInt L) h, fun h => h ▸ rfl⟩

/-- The values of a value as an integer. -/
theorem Sem.toInt_cases {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {L : Syntax S}
    [Sem L] {u : S.Val} :
    Sem.toInt L u = none ∨ ∃ z, Sem.toInt L u = some z ∧ u = Sem.vint L z := by
  rcases h : Sem.toInt L u with _ | z
  · exact .inl rfl
  · exact .inr ⟨z, rfl, Sem.vint_toInt u z h⟩

end IntMod
