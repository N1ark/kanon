import L2.Generated.Syntax
import L2.Sem
import NumMod.Sem
import NegMod.Sem

/-!
# The values of the language

Booleans and integers; an environment gives each variable a value, or none
(poison).
-/

namespace L2

open Kanon

/-- The values: booleans and integers. -/
inductive Val where
  | bool (b : Bool)
  | int (z : Int)
  deriving DecidableEq

/-- The values of a sort. -/
def Val.Of : Val → Ty → Prop
  | .bool _, t => t = .bool .TBool
  | .int _, t => t = .num .TNum

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

instance : KanonBool.Values dom where
  vbool := { inj := .bool, proj := fun | .bool b => some b | _ => none,
             proj_inj := fun _ => rfl,
             inj_proj := by intro v b h; cases v <;> cases h <;> rfl }

instance : NumMod.Values dom where
  vnum := { inj := .int, proj := fun | .int z => some z | _ => none,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v z h; cases v <;> cases h <;> rfl }

instance : NegMod.Values dom := {}

instance : Values dom where
  lookup ρ x := ρ x
  Of := Val.Of

end L2
