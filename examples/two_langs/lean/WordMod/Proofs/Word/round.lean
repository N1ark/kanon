import WordMod.Statements.Word.round
import WordMod.Lib.Rule

/-! The arm of `round` that keeps the word: a rounding is the word itself. -/

namespace WordMod

open Kanon

@[kanon_arm] theorem round_keep : Word.round.r_keep.main.Stmt := by
  intro S _ _ B LBool LCfg L _ _ _ O _ m n a _
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v _ _ e => ?_)
  · rw [Word.round.spec, L.WT_WRound] at w
    exact ⟨w.2, by rw [Word.round.spec, B.ty_node]; exact w.1.1⟩
  · simp only [Word.round.spec, Sem.ev_WRound] at e
    exact e

end WordMod
