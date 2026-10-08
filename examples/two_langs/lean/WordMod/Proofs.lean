import WordMod.Generated.Statements.Word.add
import WordMod.Generated.Statements.Word.round

/-!
# The arms of the word module that the default tactic does not prove

That which sums two literals, by the oracle `wsum`: its `Oracle.Compat` relates
it to the sum. That which checks a literal by the oracle `wcheck`: both of its
cases are the spec.
-/

namespace WordMod

open Kanon

@[kanon_arm] theorem add_lits : Word.add.r_lits.main.Stmt := by
  intro S _ _ _ _ O hO f n x _ _ y _ _
  rw [hO.word_orc.wsum]
  kanon_auto

@[kanon_arm] theorem round_check : Word.round.r_check.main.Stmt := by
  intro S _ _ _ _ O _ m n z _ _
  cases O.word_wcheck z <;> exact Sem.Refines.refl

end WordMod
