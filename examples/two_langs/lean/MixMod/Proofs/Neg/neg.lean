import MixMod.Statements.Neg.neg
import MixMod.Lifts

/-!
# The arm `-(Rem2 a) → 0`, for `a` an even literal, that the mix module adds to `neg`

The module uses the even and neg modules, which both use the num module (and
the bool module): a diamond. Their interfaces take that of the num module as the
same parameter `LNum`, so that the lemmas of the num module (`NumMod.Sem.ev_Num`,
`NumMod.Sem.toInt_vint`) and those of the two modules rewrite the goal as they
are, by `simp` and `rw`.
-/

namespace MixMod

open Kanon

@[kanon_arm] theorem neg_rem : Neg.neg.r_rem.main.Stmt := by
  intro S _ _ B LBool LNum LEven LNeg L _ _ _ _ _ O hO a t h
  rw [LEven.even_is_ev_eq] at h
  rcases hz : LEven.asEv a with _ | z
  · simp [hz, Kanon.firstSome] at h
  obtain ⟨t', rfl⟩ : ∃ t', a = B.node (LEven.EvK z) t' := ⟨_, LEven.asEv_sound a z hz⟩
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [NegMod.Neg.neg.spec, LNeg.WT_Neg, LNum.WT_Num, B.ty_node] at w ⊢
  · simp only [NegMod.Neg.neg.spec, LNeg.WT_Neg, LEven.WT_Rem2, LEven.WT_Ev,
      EvenMod.Sem.even_inv_Ev] at w
    simp only [NegMod.Neg.neg.spec, NegMod.Sem.ev_Neg, EvenMod.Sem.ev_Rem2, EvenMod.Sem.ev_Ev,
      NegMod.negV, EvenMod.rem2V, NumMod.Sem.toInt_vint, Option.bind_some, Option.map_some,
      Option.some.injEq, w.2.2.2] at e
    rw [NumMod.Sem.ev_Num, ← e]
    rfl

end MixMod
