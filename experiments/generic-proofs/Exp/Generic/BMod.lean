import Exp.Val

/-! The bool-like module `B`, proved once for any language that has it
(a generalisation of `KanonCore.BoolMod.Lang`). -/

namespace Exp.BMod

open Classical Kanon

/-- What a language must provide for the module `B`. -/
structure Lang (S : Sem) where
  make ::
  Kind : Type
  mk : Kind → S.Ty → S.Term
  tbool : S.Ty
  litK : Bool → Kind
  notK : S.Term → Kind
  iteK : S.Term → S.Term → S.Term → Kind
  eqK : S.Term → S.Term → Kind
  vb : Bool → S.Val
  db : S.Val → Option Bool
  sure_neq : S.Term → S.Term → Bool
  ty_mk : ∀ k t, S.ty (mk k t) = t
  WT_lit : ∀ b t, S.WT (mk (litK b) t) ↔ t = tbool
  WT_not : ∀ a t, S.WT (mk (notK a) t) ↔ S.ty a = tbool ∧ t = tbool ∧ S.WT a
  WT_ite : ∀ g a b t, S.WT (mk (iteK g a b) t) ↔
    S.ty g = tbool ∧ S.ty a = t ∧ S.ty b = t ∧ S.WT g ∧ S.WT a ∧ S.WT b
  WT_eq : ∀ a b t, S.WT (mk (eqK a b) t) ↔ S.ty b = S.ty a ∧ t = tbool ∧ S.WT a ∧ S.WT b
  ev_lit : ∀ ρ b t, S.ev ρ (mk (litK b) t) = some (vb b)
  ev_not : ∀ ρ a t, S.ev ρ (mk (notK a) t) = pnot vb db (S.ev ρ a)
  ev_ite : ∀ ρ g a b t, S.ev ρ (mk (iteK g a b) t) = pite db (S.ev ρ g) (S.ev ρ a) (S.ev ρ b)
  ev_eq : ∀ ρ a b t, S.ev ρ (mk (eqK a b) t) = peq vb (S.ev ρ a) (S.ev ρ b)
  db_vb : ∀ b, db (vb b) = some b
  vb_db : ∀ v b, db v = some b → v = vb b
  /-- Global law: well-typed booleans evaluate to booleans (proved per language
  by induction over ALL its nodes). -/
  ev_bool : ∀ ρ t v, S.WT t → S.ty t = tbool → S.ev ρ t = some v → ∃ b, db v = some b
  /-- Law of the extensible helper `sure_neq` (each extending module adds a case). -/
  sure_neq_sound : ∀ ρ a b u, sure_neq a b = true → S.ty a = S.ty b → S.WT a → S.WT b →
    S.ev ρ a = some u → S.ev ρ b = some u → False

/-- The rule functions (and oracles) of `B` in the model of a language. -/
structure Ops {S : Sem} (L : Lang S) where
  not_ : S.Term → S.Term
  ite : S.Term → S.Term → S.Term → S.Term
  eq : S.Term → S.Term → S.Term
  tag_le : S.Term → S.Term → Bool

structure Ops.Sound {S : Sem} {L : Lang S} (B : Ops L) : Prop where
  not_ : ∀ a, S.Refines (L.mk (L.notK a) L.tbool) (B.not_ a)
  ite : ∀ g a b, S.Refines (L.mk (L.iteK g a b) (S.ty a)) (B.ite g a b)
  eq : ∀ a b, S.Refines (L.mk (L.eqK a b) L.tbool) (B.eq a b)

namespace Lang
variable {S : Sem} (L : Lang S)

@[simp] theorem db_vb' (b : Bool) : L.db (L.vb b) = some b := L.db_vb b
theorem vb_db' {v : S.Val} {b : Bool} (h : L.db v = some b) : v = L.vb b := L.vb_db v b h
@[simp] theorem vb_inj {a b : Bool} : L.vb a = L.vb b ↔ a = b :=
  ⟨fun h => by simpa using congrArg L.db h, fun h => h ▸ rfl⟩

/-- The rewriting set of the module: typing and evaluation of its nodes. -/
theorem refines_not {a a' : S.Term} {t : S.Ty} (ha : S.Refines a a') :
    S.Refines (L.mk (L.notK a) t) (L.mk (L.notK a') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [L.WT_not] at w
    obtain ⟨wa, sa⟩ := ha.syn w.2.2
    exact ⟨(L.WT_not _ _).2 ⟨sa.trans w.1, w.2.1, wa⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.WT_not] at w; rw [L.ev_not] at e ⊢
    have := ha.ev w.2.2 ρ
    simp only [pnot, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
    obtain ⟨x, hx, b, hb, rfl⟩ := e
    exact ⟨x, this x hx, b, hb, rfl⟩

theorem refines_ite {g g' a a' b b' : S.Term} {t t' : S.Ty} (hg : S.Refines g g')
    (ha : S.Refines a a') (hb : S.Refines b b') (ht : S.WT (L.mk (L.iteK g a b) t) → t' = t) :
    S.Refines (L.mk (L.iteK g a b) t) (L.mk (L.iteK g' a' b') t') := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · have ht := ht w; subst ht
    rw [L.WT_ite] at w
    obtain ⟨h1, h2, h3, wg, wa, wb⟩ := w
    obtain ⟨wg', sg⟩ := hg.syn wg
    obtain ⟨wa', sa⟩ := ha.syn wa
    obtain ⟨wb', sb⟩ := hb.syn wb
    exact ⟨(L.WT_ite _ _ _ _).2 ⟨sg.trans h1, sa.trans h2, sb.trans h3, wg', wa', wb'⟩,
      by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.WT_ite] at w; rw [L.ev_ite] at e ⊢
    have eg := hg.ev w.2.2.2.1 ρ
    have ea := ha.ev w.2.2.2.2.1 ρ
    have eb := hb.ev w.2.2.2.2.2 ρ
    simp only [pite, Option.bind_eq_some_iff] at e ⊢
    obtain ⟨x, hx, c, hc, e⟩ := e
    refine ⟨x, eg x hx, c, hc, ?_⟩
    cases c
    · simpa using eb v (by simpa using e)
    · simpa using ea v (by simpa using e)

end Lang

set_option hygiene false in
/-- The typing and evaluation of the nodes of `B`, and the value operations. -/
macro "bmod_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Lang.ty_mk, Lang.WT_lit, Lang.WT_not, Lang.WT_ite, Lang.WT_eq, Lang.ev_lit,
    Lang.ev_not, Lang.ev_ite, Lang.ev_eq, pnot, pite, peq, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.bind_some, Option.map_some, Option.some.injEq,
    Lang.db_vb', Lang.vb_inj] $[$loc]?)

set_option hygiene false in
macro "bmod_sem" : tactic => `(tactic| (
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · bmod_simp at w ⊢; grind
  · bmod_simp at w w' e ⊢; grind [Lang.vb_db', Lang.db_vb', Lang.vb_inj]))

/-! ## The arms of the rules of `B` -/

variable {S : Sem} (L : Lang S) (B : Ops L) (hB : B.Sound)

theorem not_.lit : ∀ (b : Bool) (t : S.Ty),
    S.Refines (L.mk (L.notK (L.mk (L.litK b) t)) L.tbool) (L.mk (L.litK (!b)) L.tbool) := by
  intro b t; bmod_sem

theorem not_.nn : ∀ (a : S.Term) (t : S.Ty),
    S.Refines (L.mk (L.notK (L.mk (L.notK a) t)) L.tbool) a := by
  intro a t; bmod_sem

/-- A catch-all arm: any other node. -/
theorem not_.default : ∀ (v : S.Term),
    S.Refines (L.mk (L.notK v) L.tbool) (L.mk (L.notK v) L.tbool) :=
  fun _ => Sem.Refines.refl

theorem ite.true_ : ∀ (a b : S.Term) (t : S.Ty),
    S.Refines (L.mk (L.iteK (L.mk (L.litK true) t) a b) (S.ty a)) a := by
  intro a b t; bmod_sem

theorem ite.same : ∀ (g a a' : S.Term), decide (a = a') = true →
    S.Refines (L.mk (L.iteK g a a') (S.ty a)) a := by
  intro g a a' h; simp only [decide_eq_true_eq] at h; subst h; bmod_sem

/-- Needs the global law `ev_bool`. -/
theorem ite.bool : ∀ (g : S.Term) (t1 t2 : S.Ty),
    S.Refines (L.mk (L.iteK g (L.mk (L.litK true) t1) (L.mk (L.litK false) t2))
      (S.ty (L.mk (L.litK true) t1))) g := by
  intro g t1 t2
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · bmod_simp at w ⊢; grind
  · bmod_simp at w e
    obtain ⟨x, hx, c, hc, e⟩ := e
    rw [L.vb_db x c hc] at hx
    cases c <;> simp_all

theorem eq.same : ∀ (a b : S.Term), decide (a = b) = true →
    S.Refines (L.mk (L.eqK a b) L.tbool) (L.mk (L.litK true) L.tbool) := by
  intro a b h; simp only [decide_eq_true_eq] at h; subst h; bmod_sem

/-- Uses the extensible helper `sure_neq`. -/
theorem eq.neq : ∀ (a b : S.Term), L.sure_neq a b = true →
    S.Refines (L.mk (L.eqK a b) L.tbool) (L.mk (L.litK false) L.tbool) := by
  intro a b h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · bmod_simp at w ⊢; grind
  · bmod_simp at w e ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := e
    by_cases hxy : x = y
    · subst hxy; exact (L.sure_neq_sound ρ a b x h w.1.symm w.2.2.1 w.2.2.2 hx hy).elim
    · simp [hxy]

theorem eq.lits : ∀ (x : Bool) (t1 : S.Ty) (y : Bool) (t2 : S.Ty),
    S.Refines (L.mk (L.eqK (L.mk (L.litK x) t1) (L.mk (L.litK y) t2)) L.tbool)
      (L.mk (L.litK (decide (x = y))) L.tbool) := by
  intro x t1 y t2
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · bmod_simp at w ⊢; grind
  · bmod_simp at w e ⊢
    subst e
    cases x <;> cases y <;> simp

/-- A catch-all arm of a commutative node. -/
theorem eq.default : ∀ (a b : S.Term),
    S.Refines (L.mk (L.eqK a b) L.tbool)
      (L.mk (if B.tag_le a b then L.eqK a b else L.eqK b a) L.tbool) := by
  intro a b
  split
  · exact Sem.Refines.refl
  · refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · bmod_simp at w ⊢; grind
    · bmod_simp at w e ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := e
      exact ⟨y, hy, x, hx, by simp [eq_comm]⟩

/-- The case that `B` gives to its extensible helper `sure_neq`. -/
theorem sure_neq.bools {ρ : S.Env} {x y : Bool} {t t' : S.Ty} {u : S.Val} (h : x ≠ y)
    (ea : S.ev ρ (L.mk (L.litK x) t) = some u) (eb : S.ev ρ (L.mk (L.litK y) t') = some u) :
    False := by
  rw [L.ev_lit] at ea eb
  exact h (by simpa using (Option.some.inj ea).trans (Option.some.inj eb).symm)

end Exp.BMod
