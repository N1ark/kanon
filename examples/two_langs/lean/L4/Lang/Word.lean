import L4.Lang.Bool
import L4.Lang.Cfg
import L4.Interface.Word

/-! The language, for the word module: its laws hold by definition. -/

namespace L4

open Classical Kanon

/-- What the word module needs of the semantics: its laws hold by definition. -/
noncomputable instance wordSem : WordMod.Sem (S := sem) wordSyntax where
  vint := .int
  toInt := Val.toInt

end L4
