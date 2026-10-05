import Exp.Generic.BMod

/-! The int module `I`, which uses `B`: its interface extends that of `B`. -/

namespace Exp.IMod

open Classical Kanon

structure Lang (S : Sem) extends toB : BMod.Lang S where
  tint : S.Ty
  ilitK : Int → Kind
  addK : S.Term → S.Term → Kind
  ltK : S.Term → S.Term → Kind
  ofBoolK : S.Term → Kind
  vi : Int → S.Val
  di : S.Val → Option Int
  WT_ilit : ∀ z t, S.WT (mk (ilitK z) t) ↔ t = tint
  WT_add : ∀ a b t, S.WT (mk (addK a b) t) ↔
    S.ty a = tint ∧ S.ty b = tint ∧ t = tint ∧ S.WT a ∧ S.WT b
  WT_lt : ∀ a b t, S.WT (mk (ltK a b) t) ↔
    S.ty a = tint ∧ S.ty b = tint ∧ t = tbool ∧ S.WT a ∧ S.WT b
  WT_ofBool : ∀ a t, S.WT (mk (ofBoolK a) t) ↔ S.ty a = tbool ∧ t = tint ∧ S.WT a
  ev_ilit : ∀ ρ z t, S.ev ρ (mk (ilitK z) t) = some (vi z)
  ev_add : ∀ ρ a b t, S.ev ρ (mk (addK a b) t) = padd vi di (S.ev ρ a) (S.ev ρ b)
  ev_lt : ∀ ρ a b t, S.ev ρ (mk (ltK a b) t) = plt vb di (S.ev ρ a) (S.ev ρ b)
  ev_ofBool : ∀ ρ a t, S.ev ρ (mk (ofBoolK a) t) = pofbool vi db (S.ev ρ a)
  di_vi : ∀ z, di (vi z) = some z
  vi_di : ∀ v z, di v = some z → v = vi z

structure Ops {S : Sem} (L : Lang S) extends toB : BMod.Ops L.toB where
  add : S.Term → S.Term → S.Term
  lt : S.Term → S.Term → S.Term
  of_bool : S.Term → S.Term

structure Ops.Sound {S : Sem} {L : Lang S} (O : Ops L) : Prop
    extends toB : BMod.Ops.Sound O.toB where
  add : ∀ a b, S.Refines (L.mk (L.addK a b) L.tint) (O.add a b)
  lt : ∀ a b, S.Refines (L.mk (L.ltK a b) L.tbool) (O.lt a b)
  of_bool : ∀ a, S.Refines (L.mk (L.ofBoolK a) L.tint) (O.of_bool a)

namespace Lang
variable {S : Sem} (L : Lang S)

@[simp] theorem di_vi' (z : Int) : L.di (L.vi z) = some z := L.di_vi z
theorem vi_di' {v : S.Val} {z : Int} (h : L.di v = some z) : v = L.vi z := L.vi_di v z h
@[simp] theorem vi_inj {a b : Int} : L.vi a = L.vi b ↔ a = b :=
  ⟨fun h => by simpa using congrArg L.di h, fun h => h ▸ rfl⟩

theorem refines_add {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (L.mk (L.addK a b) t) (L.mk (L.addK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [L.WT_add] at w
    obtain ⟨wa, sa⟩ := ha.syn w.2.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2.2
    exact ⟨(L.WT_add _ _ _).2 ⟨sa.trans w.1, sb.trans w.2.1, w.2.2.1, wa, wb⟩,
      by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.WT_add] at w; rw [L.ev_add] at e ⊢
    have ea := ha.ev w.2.2.2.1 ρ
    have eb := hb.ev w.2.2.2.2 ρ
    simp only [padd, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
    obtain ⟨x, hx, y, hy, m, hm, n, hn, rfl⟩ := e
    exact ⟨x, ea x hx, y, eb y hy, m, hm, n, hn, rfl⟩

theorem refines_lt {a a' b b' : S.Term} {t : S.Ty} (ha : S.Refines a a') (hb : S.Refines b b') :
    S.Refines (L.mk (L.ltK a b) t) (L.mk (L.ltK a' b') t) := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [L.WT_lt] at w
    obtain ⟨wa, sa⟩ := ha.syn w.2.2.2.1
    obtain ⟨wb, sb⟩ := hb.syn w.2.2.2.2
    exact ⟨(L.WT_lt _ _ _).2 ⟨sa.trans w.1, sb.trans w.2.1, w.2.2.1, wa, wb⟩,
      by rw [L.ty_mk, L.ty_mk]⟩
  · rw [L.WT_lt] at w; rw [L.ev_lt] at e ⊢
    have ea := ha.ev w.2.2.2.1 ρ
    have eb := hb.ev w.2.2.2.2 ρ
    simp only [plt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e ⊢
    obtain ⟨x, hx, y, hy, m, hm, n, hn, rfl⟩ := e
    exact ⟨x, ea x hx, y, eb y hy, m, hm, n, hn, rfl⟩

end Lang

set_option hygiene false in
macro "imod_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [BMod.Lang.ty_mk, BMod.Lang.WT_lit, BMod.Lang.WT_not, BMod.Lang.WT_ite,
    BMod.Lang.WT_eq, BMod.Lang.ev_lit, BMod.Lang.ev_not, BMod.Lang.ev_ite, BMod.Lang.ev_eq,
    IMod.Lang.WT_ilit, IMod.Lang.WT_add, IMod.Lang.WT_lt, IMod.Lang.WT_ofBool, IMod.Lang.ev_ilit, IMod.Lang.ev_add,
    IMod.Lang.ev_lt, IMod.Lang.ev_ofBool,
    pnot, pite, peq, padd, plt, pofbool, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.bind_some, Option.map_some, Option.some.injEq,
    BMod.Lang.db_vb', BMod.Lang.vb_inj, IMod.Lang.di_vi', IMod.Lang.vi_inj] $[$loc]?)

set_option hygiene false in
macro "imod_sem" : tactic => `(tactic| (
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · imod_simp at w ⊢; grind
  · imod_simp at w w' e ⊢
    grind [BMod.Lang.vb_db', BMod.Lang.db_vb', BMod.Lang.vb_inj, IMod.Lang.vi_di', IMod.Lang.di_vi',
      IMod.Lang.vi_inj]))

/-! ## The arms of the rules of `I` -/

variable {S : Sem} (L : Lang S) (O : Ops L) (hO : O.Sound)

theorem add.lits : ∀ (x : Int) (t1 : S.Ty) (y : Int) (t2 : S.Ty),
    S.Refines (L.mk (L.addK (L.mk (L.ilitK x) t1) (L.mk (L.ilitK y) t2)) L.tint)
      (L.mk (L.ilitK (x + y)) L.tint) := by
  intro x t1 y t2; imod_sem

theorem add.zero : ∀ (t1 : S.Ty) (y : S.Term),
    S.Refines (L.mk (L.addK (L.mk (L.ilitK 0) t1) y) L.tint) y := by
  intro t1 y; imod_sem

/-- The distribution of `+` over a conditional (a node of `B`). -/
theorem add_ite (g a b c : S.Term) (t : S.Ty) :
    S.Refines (L.mk (L.addK (L.mk (L.iteK g a b) t) c) L.tint)
      (L.mk (L.iteK g (L.mk (L.addK a c) L.tint) (L.mk (L.addK b c) L.tint))
        (S.ty (L.mk (L.addK a c) L.tint))) := by
  imod_sem

/-- A pattern over a node of ANOTHER module (`B`'s `ite`), and calls to the
rule functions of both modules. -/
theorem add.ite (hO : O.Sound) : ∀ (g a b : S.Term) (t : S.Ty) (c : S.Term),
    S.Refines (L.mk (L.addK (L.mk (L.iteK g a b) t) c) L.tint)
      (O.ite g (O.add a c) (O.add b c)) := by
  intro g a b t c
  refine Sem.Refines.trans (add_ite L g a b c t) (Sem.Refines.trans ?_ (hO.ite _ _ _))
  refine L.refines_ite Sem.Refines.refl (hO.add a c) (hO.add b c) (fun w => ?_)
  rw [BMod.Lang.WT_ite] at w
  exact ((hO.add a c).syn w.2.2.2.2.1).2

/-- The catch-all arm of a commutative node. -/
theorem add.default : ∀ (a b : S.Term),
    S.Refines (L.mk (L.addK a b) L.tint)
      (L.mk (if O.tag_le a b then L.addK a b else L.addK b a) L.tint) := by
  intro a b
  split
  · exact Sem.Refines.refl
  · imod_sem

theorem lt.lits : ∀ (x : Int) (t1 : S.Ty) (y : Int) (t2 : S.Ty),
    S.Refines (L.mk (L.ltK (L.mk (L.ilitK x) t1) (L.mk (L.ilitK y) t2)) L.tbool)
      (L.mk (L.litK (decide (x < y))) L.tbool) := by
  intro x t1 y t2; imod_sem

theorem lt.same : ∀ (a b : S.Term), decide (a = b) = true →
    S.Refines (L.mk (L.ltK a b) L.tbool) (L.mk (L.litK false) L.tbool) := by
  intro a b h; simp only [decide_eq_true_eq] at h; subst h; imod_sem

/-- A pattern over a node of `I` holding a node of `B`. -/
theorem lt.ofbool : ∀ (b : S.Term) (t : S.Ty) (z : Int) (t2 : S.Ty), decide (1 < z) = true →
    S.Refines (L.mk (L.ltK (L.mk (L.ofBoolK b) t) (L.mk (L.ilitK z) t2)) L.tbool)
      (L.mk (L.litK true) L.tbool) := by
  intro b t z t2 h; simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
  · imod_simp at w ⊢; grind
  · imod_simp at w e ⊢
    grind [BMod.Lang.vb_db', BMod.Lang.db_vb', BMod.Lang.vb_inj, Lang.vi_di', Lang.di_vi',
      Lang.vi_inj]

theorem of_bool.true_ : ∀ (t : S.Ty),
    S.Refines (L.mk (L.ofBoolK (L.mk (L.litK true) t)) L.tint) (L.mk (L.ilitK 1) L.tint) := by
  intro t; imod_sem

theorem of_bool.false_ : ∀ (t : S.Ty),
    S.Refines (L.mk (L.ofBoolK (L.mk (L.litK false) t)) L.tint) (L.mk (L.ilitK 0) L.tint) := by
  intro t; imod_sem

/-! ### Arms that `I` adds to the rules of `B` (`extend rule`) -/

/-- `extend rule B.not_ = | lt: Not (a < b) -> b < a + 1` -/
theorem B_not_.lt (hO : O.Sound) : ∀ (a b : S.Term) (t : S.Ty),
    S.Refines (L.mk (L.notK (L.mk (L.ltK a b) t)) L.tbool)
      (O.lt b (O.add a (L.mk (L.ilitK 1) L.tint))) := by
  intro a b t
  have spec : S.Refines (L.mk (L.notK (L.mk (L.ltK a b) t)) L.tbool)
      (L.mk (L.ltK b (L.mk (L.addK a (L.mk (L.ilitK 1) L.tint)) L.tint)) L.tbool) := by
    refine Sem.Refines.intro (fun w => ?_) (fun ρ v w w' e => ?_)
    · imod_simp at w ⊢; grind
    · imod_simp at w e ⊢
      obtain ⟨x, ⟨y, hy, z, hz, m, hm, n, hn, rfl⟩, c, hc, rfl⟩ := e
      simp only [BMod.Lang.db_vb', Option.some.injEq] at hc
      subst hc
      exact ⟨z, hz, _, ⟨y, hy, m, hm, rfl⟩, n, hn, m + 1, by simp, by rw [BMod.Lang.vb_inj]; grind⟩
  refine Sem.Refines.trans spec (Sem.Refines.trans ?_ (hO.lt _ _))
  exact L.refines_lt Sem.Refines.refl (hO.add _ _)

/-- `extend rule B.eq = | ints: #x == #y -> of_bool (x = y)` -/
theorem B_eq.ints : ∀ (x : Int) (t1 : S.Ty) (y : Int) (t2 : S.Ty),
    S.Refines (L.mk (L.eqK (L.mk (L.ilitK x) t1) (L.mk (L.ilitK y) t2)) L.tbool)
      (L.mk (L.litK (decide (x = y))) L.tbool) := by
  intro x t1 y t2; imod_sem

/-- The case that `I` adds to the extensible helper `B.sure_neq` (`extend fn`). -/
theorem B_sure_neq.ints {ρ : S.Env} {x y : Int} {t t' : S.Ty} {u : S.Val} (h : x ≠ y)
    (ea : S.ev ρ (L.mk (L.ilitK x) t) = some u) (eb : S.ev ρ (L.mk (L.ilitK y) t') = some u) :
    False := by
  rw [L.ev_ilit] at ea eb
  exact h (by simpa using (Option.some.inj ea).trans (Option.some.inj eb).symm)

end Exp.IMod
