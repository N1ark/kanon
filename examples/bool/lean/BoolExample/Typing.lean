import BoolExample.Semantics

/-!
# The values of the sorts

Every value is a boolean.
-/

namespace BoolExample

open Kanon

instance : KanonBool.Typed sem where
  ev_sort _ _ v s _ _ _ := by
    cases s; cases v
    · exact .inr rfl
    · exact .inl rfl

end BoolExample
