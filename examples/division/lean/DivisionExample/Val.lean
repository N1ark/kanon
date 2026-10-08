import DivisionExample.Generated.Syntax
import DivisionExample.Sem
import DivMod.Sem

/-!
# The values of the language

Integers; an environment gives each variable a value, or none (poison).
-/

namespace DivisionExample

open Kanon

/-- The values: integers. -/
inductive Val where
  | int (z : Int)
  deriving DecidableEq

/-- The sort of a value. -/
def Val.ty : Val → Ty
  | .int _ => .int .TInt

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

instance : DivMod.Values dom where
  vint := { inj := .int, proj := fun | .int z => some z,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v z h; cases v; cases h; rfl }

instance : Values dom where
  lookup ρ x := ρ x
  sortOf := Val.ty

end DivisionExample
