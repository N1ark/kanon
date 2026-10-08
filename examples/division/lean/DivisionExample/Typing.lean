import DivisionExample.Generated.Semantics

/-!
# The values of the sorts

Every value is an integer.
-/

namespace DivisionExample

open Kanon

instance : DivMod.Typed sem where
  ev_sort _ _ v s _ _ _ := by cases s; cases v with | int z => exact ⟨z, rfl⟩

end DivisionExample
