import BoolExample.Syntax
import BoolExample.Sem
import KanonBool.Sem

/-!
# The values of the language

The values are booleans, and an environment gives each variable a boolean, or
none (poison). The bool module and the variables take them as they are.
-/

namespace BoolExample

open Kanon

/-- The values. -/
abbrev Val := Bool

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := Int → Option Bool

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

instance : KanonBool.Values dom where
  vbool := { inj := id, proj := some, proj_inj := fun _ => rfl,
             inj_proj := fun _ _ h => by cases h; rfl }

instance : Values dom where
  lookup ρ x := ρ x

end BoolExample
