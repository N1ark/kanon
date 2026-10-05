import WordMod.Lifts

/-!
# The default proof of the arms of the word module

The default arms of its rules are their specs, and the arm of `double` is the
body of its spec, the helper `twice`: `kanon_refl` unfolds it (by its law
`word_twice_eq`). The other arms are proved by hand (`Proofs/Word/`).
-/

namespace WordMod

macro "kanon_word" : tactic => `(tactic| (intro _; intros; simp only [kanon_spec]; kanon_refl))

attribute [kanon_tactic "kanon_word"] Word.add.spec Word.round.spec Word.double.spec Syntax

end WordMod
