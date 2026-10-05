import KanonBool.Sem
import NumMod.Syntax

/-!
# What the num module needs of the semantics of a language

The rules of the num module (`../num.kn`) are proved once (`NumMod`), for both
languages, over its interface `L : NumMod.Syntax S` (generated, in
`Syntax.lean`) and what the proofs need of the semantics `S`, `NumMod.Sem L`
(which extends what the bool module needs, `KanonBool.Sem`): the integers among
the values (`vint`, read back by `toInt`), and the evaluation of the nodes, by
the operations below, which both languages use in their evaluation (so that
these laws hold by definition: `kanon_law`).
-/

namespace NumMod

open Classical Kanon
open Kanon.Sem (OLe)

section
variable {V : Type} (vint : Int → V) (toInt : V → Option Int) (vbool : Bool → V)

/-- An operation on two integers; poison otherwise. -/
def op2 (f : Int → Int → V) (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (toInt x).bind fun m => (toInt y).map fun n => f m n

/-- The sum of two integers. -/
abbrev addV := op2 toInt fun m n => vint (m + n)

/-- The order of two integers. -/
abbrev ltV := op2 toInt fun m n => vbool (decide (m < n))

/-- The maximum of two integers. -/
abbrev maxV := op2 toInt fun m n => vint (max m n)

variable {toInt}

theorem op2_mono {f : Int → Int → V} {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (op2 toInt f a b) (op2 toInt f a' b') := by
  intro v e
  simp only [op2, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, y, hy, rest⟩ := e
  exact ⟨x, ha _ hx, y, hb _ hy, rest⟩

theorem op2_comm {f : Int → Int → V} (hf : ∀ m n, f m n = f n m) (a b : Option V) :
    op2 toInt f a b = op2 toInt f b a := by
  cases a <;> cases b <;> simp only [op2, Option.bind_none, Option.bind_some] <;>
    (try rfl) <;> rename_i x y <;> cases toInt x <;> cases toInt y <;> simp [hf]

end

/-- What the num module needs of the semantics `S` of a language, for its
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
  ev_Num : ∀ ρ z t, S.ev ρ (L.node (L.NumK z) t) = some (vint z) := by kanon_law
  ev_Add : ∀ ρ a b t, S.ev ρ (L.node (L.AddK a b) t) =
    addV vint toInt (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Lt : ∀ ρ a b t, S.ev ρ (L.node (L.LtK a b) t) =
    ltV toInt vbool (S.ev ρ a) (S.ev ρ b) := by kanon_law
  ev_Max : ∀ ρ a b t, S.ev ρ (L.node (L.MaxK a b) t) =
    maxV vint toInt (S.ev ρ a) (S.ev ρ b) := by kanon_law

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {L : Syntax S} [Sem L]

/-- Different integers are different values. -/
theorem vint_eq_iff {a b : Int} : vint L a = vint L b ↔ a = b :=
  ⟨fun h => by simpa [toInt_vint] using congrArg (toInt L) h, fun h => h ▸ rfl⟩

/-- The values of a value as an integer. -/
theorem toInt_cases {u : S.Val} : toInt L u = none ∨ ∃ z, toInt L u = some z ∧ u = vint L z := by
  rcases h : toInt L u with _ | z
  · exact .inl rfl
  · exact .inr ⟨z, rfl, vint_toInt u z h⟩

end Sem

end NumMod
