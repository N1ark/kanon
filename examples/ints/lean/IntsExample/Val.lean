import Generated.IntsExample.Syntax
import IntsExample.Sem
import IntMod.Sem

/-!
# The values of the language

Booleans and integers; an environment gives each variable a value, or none
(poison).
-/

namespace IntsExample

open Kanon

/-- The values: booleans and integers. -/
inductive Val where
  | bool (b : Bool)
  | int (z : Int)
  deriving DecidableEq

/-- The sort of a value. -/
def Val.ty : Val → Ty
  | .bool _ => .bool .TBool
  | .int _ => .int .TInt

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

instance : KanonBool.Values dom where
  vbool := { inj := .bool, proj := fun | .bool b => some b | _ => none,
             proj_inj := fun _ => rfl,
             inj_proj := by intro v b h; cases v <;> cases h <;> rfl }

instance : IntMod.Values dom where
  vint := { inj := .int, proj := fun | .int z => some z | _ => none,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v z h; cases v <;> cases h <;> rfl }

instance : Values dom where
  lookup ρ x := ρ x
  sortOf := Val.ty

end IntsExample
