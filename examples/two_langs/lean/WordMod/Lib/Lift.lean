import KanonCore.Proof
import WordMod.Statements

/-! The congruence of the nodes of the word module, with which `kanon_congr`
proves that the specs of its rules are monotone (`Lifts.lean`). -/

namespace WordMod

open Classical Kanon Kanon.Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
  {LBool : KanonBool.Syntax B} {LCfg : CfgMod.Syntax B} {L : Syntax B LBool LCfg}
  [KanonBool.Sem LBool] [CfgMod.Sem LCfg] [Sem L]

theorem Sem.refines_wadd {f : CfgMod.Flags} {n : Int} {a a' b b' : S.Term} {t : S.Ty}
    (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (B.node (L.WAddK f n a b) t) (B.node (L.WAddK f n a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_WAdd] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_WAdd _ _ _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_WAdd] at e ⊢
    exact addV_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem Sem.refines_wround {m : CfgMod.Rounding} {n : Int} {a a' : S.Term} {t : S.Ty}
    (ha : S.Refines a a') :
    S.Refines (B.node (L.WRoundK m n a) t) (B.node (L.WRoundK m n a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_WRound] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2
    exact ⟨(L.WT_WRound _ _ _ _).2 ⟨⟨sa.trans w.1.1, w.1.2⟩, wa⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_WRound] at e ⊢
    exact ha.ev w.2 ρ v e

attribute [kanon_congr_lemma] Sem.refines_wadd Sem.refines_wround

end WordMod
