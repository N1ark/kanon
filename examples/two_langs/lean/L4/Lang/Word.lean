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

/-- What the word module assumes of the oracles, from those of the language. -/
theorem Oracle.Compat.word {orc : Oracle} (h : orc.Compat) :
    WordMod.Oracle.Compat (S := sem) wordSyntax orc.wsum orc.wcheck :=
  { wsum := fun x y => by rw [h.wsum]; rfl }

end L4
