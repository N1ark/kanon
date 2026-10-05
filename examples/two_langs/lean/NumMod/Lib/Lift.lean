import KanonCore.Proof
import NumMod.Statements

/-!
# Refinement by congruence

The congruence lemmas of the nodes of the num module, with which `kanon_congr`
proves that its specs are monotone (`Lifts.lean`).
-/

namespace NumMod

open Classical Kanon Kanon.Sem

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {L : Syntax S} [Sem L]

theorem refines_add {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (L.node (L.AddK a b) t) (L.node (L.AddK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Add] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Add _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_Add] at e ⊢
    exact op2_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_lt {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (L.node (L.LtK a b) t) (L.node (L.LtK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Lt] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Lt _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_Lt] at e ⊢
    exact op2_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_max {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a')
    (hb : S.Refines b b') : S.Refines (L.node (L.MaxK a b) t) (L.node (L.MaxK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Max] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Max _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [L.ty_node, L.ty_node]⟩
  · rw [Sem.ev_Max] at e ⊢
    exact op2_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

attribute [kanon_congr_lemma] refines_add refines_lt refines_max

end Sem

end NumMod
