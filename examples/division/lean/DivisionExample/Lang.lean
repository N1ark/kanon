import DivisionExample.Interface

/-!
# The language, for its module

Its int module is proved once (`DivMod`), for any language that gives its
interface (which Kanon generates: `modSyntax`, in `Interface.lean`) and what it
needs of its semantics (`DivMod.Sem`): its integers, the evaluation of its nodes
and the meaning of `Nonzero`, which all hold by definition here.
-/

namespace DivisionExample

open Classical Kanon

/-- What the module proved once needs of the semantics. -/
noncomputable def lang : ModSem sem modSyntax where
  vint := .int
  toInt := Val.toInt

end DivisionExample
