import Exp.Generic.IMod

/-! The module `X` of the second language only: integer negation. -/

namespace Exp.XMod

open Classical Kanon

structure Lang (S : Sem) extends toI : IMod.Lang S where
  negK : S.Term → Kind
  WT_neg : ∀ a t, S.WT (mk (negK a) t) ↔ S.ty a = tint ∧ t = tint ∧ S.WT a
  ev_neg : ∀ ρ a t, S.ev ρ (mk (negK a) t) = pneg vi di (S.ev ρ a)

structure Ops {S : Sem} (L : Lang S) extends toI : IMod.Ops L.toI where
  neg : S.Term → S.Term

structure Ops.Sound {S : Sem} {L : Lang S} (O : Ops L) : Prop
    extends toI : IMod.Ops.Sound O.toI where
  neg : ∀ a, S.Refines (L.mk (L.negK a) L.tint) (O.neg a)

set_option hygiene false in
macro "xmod_sem" : tactic => `(tactic| (
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · iterate 2 ((try simp only [XMod.Lang.WT_neg] at w ⊢); (try imod_simp at w ⊢))
    grind
  · iterate 2 ((try simp only [XMod.Lang.WT_neg, XMod.Lang.ev_neg, pneg] at w w' e ⊢); (try imod_simp at w w' e ⊢))
    grind [BMod.Lang.vb_db', BMod.Lang.db_vb', BMod.Lang.vb_inj, IMod.Lang.vi_di',
      IMod.Lang.di_vi', IMod.Lang.vi_inj]))

variable {S : Sem} (L : Lang S)

theorem neg.lit : ∀ (x : Int) (t : S.Ty),
    S.Refines (L.mk (L.negK (L.mk (L.ilitK x) t)) L.tint) (L.mk (L.ilitK (-x)) L.tint) := by
  intro x t; xmod_sem

theorem neg.nn : ∀ (a : S.Term) (t : S.Ty),
    S.Refines (L.mk (L.negK (L.mk (L.negK a) t)) L.tint) a := by
  intro a t; xmod_sem

/-- `extend rule I.add = | negself: a + Neg a -> #0` -/
theorem I_add.negself : ∀ (a a' : S.Term) (t : S.Ty), decide (a = a') = true →
    S.Refines (L.mk (L.addK a (L.mk (L.negK a') t)) L.tint) (L.mk (L.ilitK 0) L.tint) := by
  intro a a' t h; simp only [decide_eq_true_eq] at h; subst h; xmod_sem

end Exp.XMod
