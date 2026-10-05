import KanonCore.Proof
import EvenMod.Statements

/-! The congruence of `Rem2`, with which `kanon_congr` proves that the spec of
`rem2` is monotone (`Lifts.lean`). -/

namespace EvenMod

open Classical Kanon Kanon.Sem

theorem Sem.refines_rem2 {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty]
    {B : Kanon.Base S} {LBool : KanonBool.Syntax B} {LNum : NumMod.Syntax B LBool}
    {L : Syntax B LBool LNum} [KanonBool.Sem LBool] [NumMod.Sem LNum] [Sem L] {a a' : S.Term}
    {t : S.Ty} (ha : S.Refines a a') :
    S.Refines (B.node (L.Rem2K a) t) (B.node (L.Rem2K a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Rem2] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2
    exact ⟨(L.WT_Rem2 _ _).2 ⟨⟨sa.trans w.1.1, w.1.2⟩, wa⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Rem2] at e ⊢
    exact rem2V_mono (ha.ev w.2 ρ) v e

attribute [kanon_congr_lemma] Sem.refines_rem2

end EvenMod
