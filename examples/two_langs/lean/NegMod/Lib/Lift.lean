import KanonCore.Proof
import NegMod.Statements

/-! The congruence of `Neg`, with which `kanon_congr` proves that the spec of
`neg` is monotone (`Lifts.lean`). -/

namespace NegMod

open Classical Kanon Kanon.Sem

theorem Sem.refines_neg {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {L : Syntax S}
    [Sem L] {a a' : S.Term} {t : S.Ty} (ha : S.Refines a a') :
    S.Refines (L.node (L.NegK a) t) (L.node (L.NegK a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Neg] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2
    exact ⟨(L.WT_Neg _ _).2 ⟨⟨sa.trans w.1.1, w.1.2⟩, wa⟩, by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_Neg] at e ⊢
    exact negV_mono (ha.ev w.2 ρ) v e

attribute [kanon_congr_lemma] Sem.refines_neg

end NegMod
