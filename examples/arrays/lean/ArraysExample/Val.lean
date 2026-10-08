import ArraysExample.Generated.Syntax
import ArraysExample.Vec.Sem

/-!
# The values of the language

Integers and arrays of integers. There are no variables.
-/

namespace ArraysExample

open Kanon

/-- The values: integers and arrays of integers. -/
inductive Val where
  | int (z : Int)
  | vec (a : Array Int)
  deriving DecidableEq

/-- No variables. -/
abbrev Env := Unit

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

instance : Vec.Values dom where
  vint := { inj := .int, proj := fun | .int z => some z | _ => none,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v z h; cases v <;> cases h <;> rfl }
  vvec := { inj := .vec, proj := fun | .vec a => some a | _ => none,
            proj_inj := fun _ => rfl,
            inj_proj := by intro v z h; cases v <;> cases h <;> rfl }

end ArraysExample
