import CfgMod.Types

/-! The abstract type of the cfg module that Lean does not have: `blob`, some
bits. (`label` is Lean's `String`.) -/

namespace CfgMod

/-- Some bits. -/
structure Blob where
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

end CfgMod
