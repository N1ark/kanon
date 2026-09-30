import BoolExample.Statements

/-!
# Refinement by congruence

The lemmas that reduce a refinement to its typing and value halves
(`Refines.intro`), and the congruence of refinement, with which `kanon_congr`
proves the monotonicity of the specs (`Lifts.lean`): the result of a rule
function called on terms that refine `a` and `b` refines its spec on `a` and
`b`.
-/

namespace BoolExample

open Kanon

/-- The language has a single type. -/
theorem Ty.eq_all (a b : Ty) : a = b := by cases a; cases b; rfl

theorem eval_WT {ρ : Env} {t : Term} {v : Bool} (e : eval ρ t = some v) : t.WT := by
  unfold eval at e; split at e
  · assumption
  · cases e

theorem eval_eq_ev {ρ : Env} {t : Term} (w : t.WT) : eval ρ t = ev ρ t := by
  simp [eval, w]

/-- A refinement, from its typing half and its value half on well-typed terms. -/
theorem Refines.intro {s r : Term} (hw : s.WT → r.WT ∧ r.ty = s.ty)
    (he : ∀ ρ v, s.WT → r.WT → ev ρ s = some v → ev ρ r = some v) : Refines s r :=
  ⟨hw, fun ρ v e => by
    have w := eval_WT e
    have w' := (hw w).1
    rw [eval_eq_ev w] at e
    rw [eval_eq_ev w']
    exact he ρ v w w' e⟩

/-! ## Monotonicity of the operators -/

/-- `b` is `a`, or `a` is poison. -/
def OLe (a b : Option Bool) : Prop := ∀ x, a = some x → b = some x

theorem Refines.ev_le {a a' : Term} (h : Refines a a') (w : a.WT) (ρ : Env) :
    OLe (ev ρ a) (ev ρ a') := fun x e => by
  have := h.2 ρ x (by rw [eval_eq_ev w]; exact e)
  rwa [eval_eq_ev (h.1 w).1] at this

theorem evUnop_mono {op a a'} (ha : OLe a a') : OLe (evUnop op a) (evUnop op a') := by
  intro x h
  cases op <;> rcases a with _ | _ | _ <;> simp_all [OLe, evUnop]

theorem evBinop_mono {op a a' b b'} (ha : OLe a a') (hb : OLe b b') :
    OLe (evBinop op a b) (evBinop op a' b') := by
  intro x h
  cases op <;> rcases a with _ | _ | _ <;> rcases a' with _ | _ | _ <;>
    rcases b with _ | _ | _ <;> rcases b' with _ | _ | _ <;> simp_all [OLe, evBinop, pand, por]

theorem evTriop_mono {op a a' b b' c c'} (ha : OLe a a') (hb : OLe b b') (hc : OLe c c') :
    OLe (evTriop op a b c) (evTriop op a' b' c') := by
  intro x h
  cases op
  rcases a with _ | _ | _ <;> simp only [evTriop, reduceCtorEq] at h
  · rw [ha _ rfl]; exact hc x h
  · rw [ha _ rfl]; exact hb x h

/-! ## Congruence -/

theorem Refines.unop {op : Unop} {a a' : Term} {t : Ty} (ha : Refines a a') :
    Refines (.mk (.Unop op a) t) (.mk (.Unop op a') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> simp only [Term.WT] at w
  · obtain ⟨wa, ea⟩ := ha.1 w.2
    exact ⟨⟨by rw [ea]; exact w.1, wa⟩, rfl⟩
  · simp only [ev] at e ⊢
    exact evUnop_mono (ha.ev_le w.2 ρ) v e

theorem Refines.binop {op : Binop} {a a' b b' : Term} {t : Ty} (ha : Refines a a')
    (hb : Refines b b') : Refines (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t) := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> simp only [Term.WT] at w
  · obtain ⟨wa, ea⟩ := ha.1 w.2.1
    obtain ⟨wb, eb⟩ := hb.1 w.2.2
    exact ⟨⟨by rw [ea, eb]; exact w.1, wa, wb⟩, rfl⟩
  · simp only [ev] at e ⊢
    exact evBinop_mono (ha.ev_le w.2.1 ρ) (hb.ev_le w.2.2 ρ) v e

theorem Refines.triop {op : Triop} {a a' b b' c c' : Term} {t t' : Ty} (ha : Refines a a')
    (hb : Refines b b') (hc : Refines c c') :
    Refines (.mk (.Triop op a b c) t) (.mk (.Triop op a' b' c') t') := by
  refine Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_) <;> simp only [Term.WT] at w
  · obtain ⟨wa, ea⟩ := ha.1 w.2.1
    obtain ⟨wb, eb⟩ := hb.1 w.2.2.1
    obtain ⟨wc, ec⟩ := hc.1 w.2.2.2
    exact ⟨⟨by rw [ea, eb, ec, Ty.eq_all t' t]; exact w.1, wa, wb, wc⟩, Ty.eq_all _ _⟩
  · simp only [ev] at e ⊢
    exact evTriop_mono (ha.ev_le w.2.1 ρ) (hb.ev_le w.2.2.1 ρ) (hc.ev_le w.2.2.2 ρ) v e

/-- Proves `Refines s s'`, where `s'` is `s` with some of its subterms replaced
by terms that refine them (hypotheses of the context). -/
macro_rules
  | `(tactic| kanon_congr) => `(tactic| first
      | exact Refines.refl
      | assumption
      | ((first
          | apply Refines.unop
          | apply Refines.binop
          | apply Refines.triop) <;> kanon_congr))

end BoolExample
