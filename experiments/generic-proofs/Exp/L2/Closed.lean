import Exp.L2.Step

/-! Option A (status quo): the arms of language 2 proved directly on its closed
terms, and the soundness of its step functions. -/

set_option linter.unusedVariables false

noncomputable section

namespace Exp.L2.Closed

open Classical Kanon

set_option hygiene false in
macro "l2_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [sem, Term.WT, Term.ty_mk, ev, B.not_.spec, B.ite.spec, B.eq.spec, I.add.spec,
    I.lt.spec, I.of_bool.spec, X.neg.spec, pnot, pite, peq, padd, plt, pofbool, pneg, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.bind_some, Option.map_some, Option.some.injEq,
    Val.toBool_eq_some, Val.toInt_eq_some, Val.bool.injEq, Val.int.injEq, exists_eq_left] $[$loc]?)

set_option hygiene false in
macro "l2_sem" : tactic => `(tactic| (
  refine Refines.intro' (fun w => ?_) (fun ρ v w w' e => ?_)
  · l2_simp at w ⊢; grind
  · simp only [sem, Term.WT, Term.ty_mk, ev, B.not_.spec, B.ite.spec, B.eq.spec, I.add.spec,
      I.lt.spec, I.of_bool.spec, X.neg.spec] at w w' e ⊢
    l2_cases
    all_goals (try simp_all [pnot, pite, peq, padd, plt, pofbool, pneg, Val.toBool, Val.toInt])
    all_goals (try omega)
    all_goals (subst_vars; congr 1; (try split) <;> grind)))

theorem refines_ite {g g' a a' b b' : Term} {t t' : Ty} (hg : Refines g g')
    (ha : Refines a a') (hb : Refines b b') (ht : (Term.mk (.BIte g a b) t).WT → t' = t) :
    Refines (.mk (.BIte g a b) t) (.mk (.BIte g' a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ht := ht w; subst ht
    obtain ⟨h1, h2, h3, wg, wa, wb⟩ := w
    obtain ⟨wg', sg⟩ := hg.syn wg
    obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨⟨sg.trans h1, sa.trans h2, sb.trans h3, wg', wa', wb'⟩, rfl⟩
  · have eg := hg.ev w.2.2.2.1 ρ
    have ea := ha.ev w.2.2.2.2.1 ρ
    have eb := hb.ev w.2.2.2.2.2 ρ
    simp only [sem, ev, pite, Option.bind_eq_some_iff] at e ⊢
    obtain ⟨x, hx, c, hc, e⟩ := e
    refine ⟨x, eg x hx, c, hc, ?_⟩
    cases c
    · simpa using eb v (by simpa using e)
    · simpa using ea v (by simpa using e)

theorem refines_add {a a' b b' : Term} {t : Ty} (ha : Refines a a') (hb : Refines b b') :
    Refines (.mk (.Add a b) t) (.mk (.Add a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨wa, sa⟩ := ha.syn w.2.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2.2
    exact ⟨⟨sa.trans w.1, sb.trans w.2.1, w.2.2.1, wa, wb⟩, rfl⟩
  · have ea := ha.ev w.2.2.2.1 ρ
    have eb := hb.ev w.2.2.2.2 ρ
    simp only [sem, ev, padd, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
    obtain ⟨x, hx, y, hy, m, hm, n, hn, rfl⟩ := e
    exact ⟨x, ea x hx, y, eb y hy, m, hm, n, hn, rfl⟩

theorem refines_lt {a a' b b' : Term} {t : Ty} (ha : Refines a a') (hb : Refines b b') :
    Refines (.mk (.Lt a b) t) (.mk (.Lt a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · obtain ⟨wa, sa⟩ := ha.syn w.2.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2.2
    exact ⟨⟨sa.trans w.1, sb.trans w.2.1, w.2.2.1, wa, wb⟩, rfl⟩
  · have ea := ha.ev w.2.2.2.1 ρ
    have eb := hb.ev w.2.2.2.2 ρ
    simp only [sem, ev, plt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
    obtain ⟨x, hx, y, hy, m, hm, n, hn, rfl⟩ := e
    exact ⟨x, ea x hx, y, eb y hy, m, hm, n, hn, rfl⟩

theorem B.not_.lit : B.not_.lit.Stmt := by intro O hO b t; l2_sem
theorem B.not_.nn : B.not_.nn.Stmt := by intro O hO a t; l2_sem
theorem B.not_.lt : B.not_.lt.Stmt := by
  intro O hO a b t
  have spec : Refines (L2.B.not_.spec (.mk (.Lt a b) t))
      (.mk (.Lt b (.mk (.Add a (.mk (.ILit 1) .TInt)) .TInt)) .TBool) := by l2_sem
  refine Sem.Refines.trans spec (Sem.Refines.trans ?_ (hO.lt _ _))
  exact refines_lt Sem.Refines.refl (hO.add _ _)
theorem B.not_.default : B.not_.default.Stmt := fun _ _ _ => Sem.Refines.refl
theorem B.ite.true_ : B.ite.true_.Stmt := by intro O hO a b t; l2_sem
theorem B.ite.same : B.ite.same.Stmt := by
  intro O hO g a b h; simp only [decide_eq_true_eq] at h; subst h; l2_sem
theorem B.ite.bool : B.ite.bool.Stmt := by intro O hO g t1 t2; l2_sem
theorem B.eq.ints : B.eq.ints.Stmt := by intro O hO x t1 y t2; l2_sem
theorem B.eq.same : B.eq.same.Stmt := by
  intro O hO a b h; simp only [decide_eq_true_eq] at h; subst h; l2_sem
theorem B.eq.neq : B.eq.neq.Stmt := by
  intro O hO a b h
  rcases L2.B.sure_neq_cases h with ⟨x, y, t, t', rfl, rfl, hxy⟩ | ⟨x, y, t, t', rfl, rfl, hxy⟩
  all_goals l2_sem
theorem B.eq.lits : B.eq.lits.Stmt := by intro O hO x t1 y t2; l2_sem
theorem B.eq.default : B.eq.default.Stmt := by
  intro O hO a b
  split
  · exact Sem.Refines.refl
  · l2_sem
theorem I.add.lits : I.add.lits.Stmt := by intro O hO x t1 y t2; l2_sem
theorem I.add.zero : I.add.zero.Stmt := by intro O hO t1 b; l2_sem
theorem I.add.ite : I.add.ite.Stmt := by
  intro O hO g x y t b
  have spec : Refines (L2.I.add.spec (.mk (.BIte g x y) t) b)
      (.mk (.BIte g (.mk (.Add x b) .TInt) (.mk (.Add y b) .TInt)) .TInt) := by
    refine Refines.intro' (fun w => ?_) (fun ρ v w w' e => ?_)
    · l2_simp at w ⊢; grind
    · simp only [sem, Term.WT, Term.ty_mk, ev, L2.I.add.spec] at w w' e ⊢
      simp only [pite, padd, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Val.toBool_eq_some, Val.toInt_eq_some] at e ⊢
      obtain ⟨x', ⟨gx, hg, c, rfl, hx⟩, y', hy, m, rfl, n, rfl, rfl⟩ := e
      refine ⟨_, hg, c, rfl, ?_⟩
      cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hx ⊢
      all_goals simp [hx, hy, Val.toInt]
  refine Sem.Refines.trans spec (Sem.Refines.trans ?_ (hO.ite _ _ _))
  exact refines_ite Sem.Refines.refl (hO.add x b) (hO.add y b) (fun w => ((hO.add x b).syn w.2.2.2.2.1).2)
theorem I.add.negself : I.add.negself.Stmt := by
  intro O hO a a' t h; simp only [decide_eq_true_eq] at h; subst h; l2_sem
theorem X.neg.lit : X.neg.lit.Stmt := by intro O hO x t; l2_sem
theorem X.neg.nn : X.neg.nn.Stmt := by intro O hO a t; l2_sem
theorem X.neg.default : X.neg.default.Stmt := fun _ _ _ => Sem.Refines.refl
theorem I.add.default : I.add.default.Stmt := by
  intro O hO a b
  split
  · exact Sem.Refines.refl
  · l2_sem
theorem I.lt.lits : I.lt.lits.Stmt := by intro O hO x t1 y t2; l2_sem
theorem I.lt.same : I.lt.same.Stmt := by
  intro O hO a b h; simp only [decide_eq_true_eq] at h; subst h; l2_sem
theorem I.lt.ofbool : I.lt.ofbool.Stmt := by
  intro O hO c t z t2 h; simp only [decide_eq_true_eq] at h; l2_sem
theorem I.lt.default : I.lt.default.Stmt := fun _ _ _ _ => Sem.Refines.refl
theorem I.of_bool.true_ : I.of_bool.true_.Stmt := by intro O hO t; l2_sem
theorem I.of_bool.false_ : I.of_bool.false_.Stmt := by intro O hO t; l2_sem
theorem I.of_bool.default : I.of_bool.default.Stmt := fun _ _ _ => Sem.Refines.refl
theorem B.ite.default : B.ite.default.Stmt := fun _ _ _ _ _ => Sem.Refines.refl

theorem steps_sound (O : Ops) (hO : O.Sound) :
    (∀ v, Refines (L2.B.not_.spec v) (L2.B.not_.step O v)) ∧
    (∀ g a b, Refines (L2.B.ite.spec g a b) (L2.B.ite.step O g a b)) ∧
    (∀ a b, Refines (L2.B.eq.spec a b) (L2.B.eq.step O a b)) ∧
    (∀ a b, Refines (L2.I.add.spec a b) (L2.I.add.step O a b)) ∧
    (∀ a b, Refines (L2.I.lt.spec a b) (L2.I.lt.step O a b)) ∧
    (∀ a, Refines (L2.I.of_bool.spec a) (L2.I.of_bool.step O a)) ∧
    (∀ a, Refines (L2.X.neg.spec a) (L2.X.neg.step O a)) :=
  ⟨L2.B.not_.step_sound B.not_.lit B.not_.nn B.not_.lt B.not_.default O hO,
   L2.B.ite.step_sound B.ite.true_ B.ite.same B.ite.bool B.ite.default O hO,
   L2.B.eq.step_sound B.eq.ints B.eq.same B.eq.neq B.eq.lits B.eq.default O hO,
   L2.I.add.step_sound I.add.lits I.add.zero I.add.ite I.add.negself I.add.default O hO,
   L2.I.lt.step_sound I.lt.lits I.lt.same I.lt.ofbool I.lt.default O hO,
   L2.I.of_bool.step_sound I.of_bool.true_ I.of_bool.false_ I.of_bool.default O hO,
   L2.X.neg.step_sound X.neg.lit X.neg.nn X.neg.default O hO⟩

end Exp.L2.Closed
