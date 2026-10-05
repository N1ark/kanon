import KanonCore.Proof
import KanonBool.Statements

/-!
# Refinement by congruence

The congruence lemmas of the nodes of the bool module, with which `kanon_congr`
proves that the specs are monotone (`Lifts.lean`).
-/

namespace KanonBool

open Classical Kanon Kanon.Sem

namespace Sem

variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S} {L : Syntax B} [Sem L]

theorem refines_not {a a' : S.Term} {t : S.Ty} (ha : S.Refines a a') :
    S.Refines (B.node (L.NotK a) t) (B.node (L.NotK a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [L.WT_Not] at w
    obtain ⟨wa, sa⟩ := ha.syn w.2
    exact ⟨(L.WT_Not _ _).2 ⟨⟨sa.trans w.1.1, w.1.2⟩, wa⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [L.WT_Not] at w
    rw [Sem.ev_Not] at e ⊢
    exact pnot_mono (ha.ev w.2 ρ) v e

theorem refines_and {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (B.node (L.AndK a b) t) (B.node (L.AndK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_And] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_And _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_And] at e ⊢
    exact pand_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_or {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (B.node (L.OrK a b) t) (B.node (L.OrK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Or] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Or _ _ _).2 ⟨⟨sa.trans w.1.1, sb.trans w.1.2.1, w.1.2.2⟩, wa, wb⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Or] at e ⊢
    exact por_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

theorem refines_eq {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (B.node (L.EqK a b) t) (B.node (L.EqK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> rw [L.WT_Eq] at w
  · obtain ⟨wa, sa⟩ := ha.syn w.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2
    exact ⟨(L.WT_Eq _ _ _).2 ⟨⟨by rw [sa, sb]; exact w.1.1, w.1.2⟩, wa, wb⟩,
      by rw [B.ty_node, B.ty_node]⟩
  · rw [Sem.ev_Eq] at e ⊢
    exact peq_mono (ha.ev w.2.1 ρ) (hb.ev w.2.2 ρ) v e

/-- The sort of an `ite`, which the spec of `ite` writes `ty if_`, is that of
the refined branch on the right. -/
theorem refines_ite {g g' a a' b b' : S.Term} {t t' : S.Ty} (hg : S.Refines g g')
    (ha : S.Refines a a') (hb : S.Refines b b') (ht : S.WT (B.node (L.IteK g a b) t) → t' = t) :
    S.Refines (B.node (L.IteK g a b) t) (B.node (L.IteK g' a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ht := ht w
    subst ht
    rw [L.WT_Ite] at w
    obtain ⟨⟨h1, h2, h3⟩, wg, wa, wb⟩ := w
    obtain ⟨wg', sg⟩ := hg.syn wg
    obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨(L.WT_Ite _ _ _ _).2 ⟨⟨sg.trans h1, by rw [sb, sa]; exact h2, by rw [sa]; exact h3⟩,
      wg', wa', wb'⟩, by rw [B.ty_node, B.ty_node]⟩
  · rw [L.WT_Ite] at w
    rw [Sem.ev_Ite] at e ⊢
    exact pite_mono (hg.ev w.2.1 ρ) (ha.ev w.2.2.1 ρ) (hb.ev w.2.2.2 ρ) v e

attribute [kanon_congr_lemma] refines_not refines_and refines_or refines_eq refines_ite

end Sem

/-- The side goal of `refines_ite` when the spec of `ite` is lifted: the sort of
the refined branch is that of the branch. -/
macro_rules | `(tactic| kanon_congr_side) => `(tactic|
  (intro w
   refine Kanon.Sem.ty_refines ?_ ((KanonBool.Syntax.WT_Ite _ _ _ _ _).1 w).2.2.1
   assumption))

end KanonBool
