import KanonCore.BoolMod.Tactic

/-!
# The rules of the bool module, proved once

The arms of the rules of `modules/bool.kn` (with those that Kanon derives from
the laws of `modules/bool.knl` and the swaps of commutative operands), for any
language `L` that uses the module and the model `B` of the module in that
language. The statement `Kanon.BoolMod.f.r_rule.arm` is that of the arm
`f.r_rule.arm` of a language, whose generated proof is this theorem applied to
the language (`fun O hO => Kanon.BoolMod.f.r_rule.arm boolLang O.bool hO.bool`).

The statements are written as Kanon generates those of the arms, with the
nodes of `L` and the functions of `B`. Most arms are proved by `kanon_bool`
(`KanonCore.BoolMod.Tactic`).
-/

namespace Kanon.BoolMod

open Classical Kanon

/-! ## Lemmas -/

section
variable {S : Sem} {L : Lang S}

/-- `a == x && a == y` (with the equalities in either order) refines `false`,
for `x` and `y` surely different. -/
theorem refines_and_eq_neq {p1 q1 p2 q2 x y a : S.Term} {t1 t2 : S.Ty}
    (o1 : (p1 = a ∧ q1 = x) ∨ (p1 = x ∧ q1 = a)) (o2 : (p2 = a ∧ q2 = y) ∨ (p2 = y ∧ q2 = a))
    (hn : L.sure_neq x y = true) :
    S.Refines (L.mkAnd (L.mk (L.eqK p1 q1) t1) (L.mk (L.eqK p2 q2) t2)) L.vfalse := by
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [Lang.WT_lit, Lang.ty_mk]
  simp only [Lang.mkAnd, Lang.WT_and, Lang.WT_eq, Lang.ty_mk] at w
  obtain ⟨-, -, -, ⟨h1, -, w1, w1'⟩, ⟨h2, -, w2, w2'⟩⟩ := w
  simp only [Lang.mkAnd, Lang.vfalse, Lang.ev_and, Lang.ev_eq, Lang.ev_lit] at e ⊢
  rw [pand_eq_some] at e
  rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨e1, e2, -⟩
  · rfl
  · rfl
  rw [peq_eq_some] at e1 e2
  obtain ⟨u1, u1', e1, e1', hu1⟩ := e1
  obtain ⟨u2, u2', e2, e2', hu2⟩ := e2
  rw [Lang.vbool_eq_iff, eq_comm, decide_eq_true_iff] at hu1 hu2
  subst hu1 hu2
  have hx : S.ty x = S.ty a ∧ S.WT x ∧ ∃ u, S.ev ρ x = some u ∧ S.ev ρ a = some u := by
    rcases o1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h1.symm, w1', u1, e1', e1⟩
    · exact ⟨h1, w1, u1, e1, e1'⟩
  have hy : S.ty y = S.ty a ∧ S.WT y ∧ ∃ u, S.ev ρ y = some u ∧ S.ev ρ a = some u := by
    rcases o2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h2.symm, w2', u2, e2', e2⟩
    · exact ⟨h2, w2, u2, e2, e2'⟩
  obtain ⟨tx, wx, ux, ex, ea⟩ := hx
  obtain ⟨ty, wy, uy, ey, ea'⟩ := hy
  rw [ea] at ea'; cases ea'
  exact (L.sure_neq_sound ρ x y ux hn (tx.trans ty.symm) wx wy ex ey).elim

theorem mapM_eq_some {α β : Type} {f : α → Option β} {d : β} : ∀ {l : List α} {vs : List β},
    l.mapM f = some vs ↔ (∀ t ∈ l, ∃ v, f t = some v) ∧ vs = l.map (fun t => (f t).getD d)
  | [], vs => by simp [eq_comm]
  | t :: ts, vs => by
    have ih := @mapM_eq_some _ _ f d ts
    rw [List.mapM_cons]
    rcases h : f t with _ | v
    · simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq, false_iff]
      rintro ⟨h1, -⟩
      obtain ⟨v, hv⟩ := h1 t (by simp)
      rw [h] at hv; cases hv
    · rcases hts : ts.mapM f with _ | ws
      · simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq, false_iff]
        rintro ⟨h1, -⟩
        have := (ih (vs := ts.map (fun t => (f t).getD d))).2 ⟨fun t ht => h1 t (by simp [ht]), rfl⟩
        rw [hts] at this; cases this
      · obtain ⟨h1, rfl⟩ := ih.1 hts
        simp only [Option.bind_eq_bind, Option.bind_some, List.map_cons, h,
          Option.getD_some, pure, Option.some.injEq, List.mem_cons, eq_comm (a := vs)]
        constructor
        · rintro rfl; exact ⟨fun t' ht' => ht'.elim (fun e => e ▸ ⟨v, h⟩) (h1 t'), rfl⟩
        · exact fun h' => h'.2

variable {B : Ops L} (hB : B.Sound)
include hB

theorem distinct_check_one_true {a : S.Term} : ∀ {rest : List S.Term},
    B.distinct_check_one a rest = some true → ∀ b ∈ rest, L.sure_neq a b = true
  | [], _ => by simp
  | b :: rest, h => by
    rw [hB.distinct_check_one_cons] at h
    split at h
    · cases h
    split at h
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · assumption
      · exact distinct_check_one_true h c hc
    · cases h

theorem distinct_check_one_false {a : S.Term} : ∀ {rest : List S.Term},
    B.distinct_check_one a rest = some false → a ∈ rest
  | [], h => by rw [hB.distinct_check_one_nil] at h; cases h
  | b :: rest, h => by
    rw [hB.distinct_check_one_cons] at h
    split at h
    · rename_i he; rw [of_decide_eq_true he]; exact List.mem_cons_self
    split at h
    · exact List.mem_cons_of_mem _ (distinct_check_one_false h)
    · cases h

theorem distinct_check_true : ∀ {l : List S.Term},
    B.distinct_check l = some true → l.Pairwise (fun a b => L.sure_neq a b = true)
  | [], _ => .nil
  | a :: rest, h => by
    rw [hB.distinct_check_cons] at h
    split at h
    · exact .cons (distinct_check_one_true hB ‹_›) (distinct_check_true h)
    · exact absurd h ‹_›

theorem distinct_check_false : ∀ {l : List S.Term}, B.distinct_check l = some false → ¬ l.Nodup
  | [], h => by rw [hB.distinct_check_nil] at h; cases h
  | a :: rest, h => by
    rw [hB.distinct_check_cons] at h
    rw [List.nodup_cons]
    split at h
    · exact fun h' => distinct_check_false h h'.2
    · exact fun h' => h'.1 (distinct_check_one_false hB h)

end

/-- The value of a `Distinct` that is not poison: its operands are not poison,
and it says whether their values are pairwise different. -/
theorem ev_distinct_eq_some {S : Sem} {L : Lang S} {ρ : S.Env} {l : List S.Term} {t : S.Ty}
    {v : S.Val} (e : S.ev ρ (L.mk (L.distinctK l) t) = some v) :
    (∀ x ∈ l, ∃ u, S.ev ρ x = some u) ∧
      v = L.vbool (decide (l.map fun x => (S.ev ρ x).getD (L.vbool false)).Nodup) := by
  rw [L.ev_distinct, pdistinct, Option.map_eq_some_iff] at e
  obtain ⟨vs, hvs, rfl⟩ := e
  obtain ⟨h, rfl⟩ := (mapM_eq_some (d := L.vbool false)).1 hvs
  exact ⟨h, rfl⟩

theorem ev_distinct {S : Sem} {L : Lang S} {ρ : S.Env} {l : List S.Term} {t : S.Ty}
    (h : ∀ x ∈ l, ∃ u, S.ev ρ x = some u) :
    S.ev ρ (L.mk (L.distinctK l) t) =
      some (L.vbool (decide (l.map fun x => (S.ev ρ x).getD (L.vbool false)).Nodup)) := by
  rw [L.ev_distinct, (mapM_eq_some (d := L.vbool false)).2 ⟨h, rfl⟩]; rfl

/-! ## The arms -/

set_option linter.unusedSectionVars false

variable {S : Sem} (L : Lang S) (B : Ops L) (hB : B.Sound)
include hB

theorem Bool.and_.r_same.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    (decide (v1 = v2)) = true →
    S.Refines (L.mkAnd v1 v2)
    (v1) := by
  kanon_bool

theorem Bool.and_.r_false_.main :
    ∀ (v2 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkAnd (L.mk (L.litK false) t__2) v2)
    (L.vfalse) := by
  kanon_bool

theorem Bool.and_.r_false_.swap :
    ∀ (v1 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkAnd v1 (L.mk (L.litK false) t__2))
    (L.vfalse) := by
  kanon_bool

theorem Bool.and_.r_true_.main :
    ∀ (v2 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkAnd (L.mk (L.litK true) t__2) v2)
    (v2) := by
  kanon_bool

theorem Bool.and_.r_true_.swap :
    ∀ (v1 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkAnd v1 (L.mk (L.litK true) t__2))
    (v1) := by
  kanon_bool

theorem Bool.and_.r_not.main :
    ∀ (v1 : S.Term) (kanon__3 : S.Term) (t__4 : S.Ty),
    (decide (v1 = kanon__3)) = true →
    S.Refines (L.mkAnd v1 (L.mk (L.notK kanon__3) t__4))
    (L.vfalse) := by
  kanon_bool

theorem Bool.and_.r_not.swap :
    ∀ (v2 : S.Term) (kanon__3 : S.Term) (t__4 : S.Ty),
    (decide (v2 = kanon__3)) = true →
    S.Refines (L.mkAnd (L.mk (L.notK kanon__3) t__4) v2)
    (L.vfalse) := by
  kanon_bool

theorem Bool.and_.r_and_.main :
    ∀ (v2 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkAnd (L.mk (L.andK a w__3) t__4) v2)
    ((L.mk (L.andK a w__3) t__4)) := by
  kanon_bool

theorem Bool.and_.r_and_.swap1 :
    ∀ (v2 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkAnd (L.mk (L.andK w__3 a) t__4) v2)
    ((L.mk (L.andK w__3 a) t__4)) := by
  kanon_bool

theorem Bool.and_.r_and_.swap2 :
    ∀ (v1 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkAnd v1 (L.mk (L.andK a w__3) t__4))
    ((L.mk (L.andK a w__3) t__4)) := by
  kanon_bool

theorem Bool.and_.r_and_.swap1_swap2 :
    ∀ (v1 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkAnd v1 (L.mk (L.andK w__3 a) t__4))
    ((L.mk (L.andK w__3 a) t__4)) := by
  kanon_bool

theorem Bool.and_.r_or_.main :
    ∀ (v2 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkAnd (L.mk (L.orK a w__3) t__4) v2)
    (a) := by
  kanon_bool

theorem Bool.and_.r_or_.swap1 :
    ∀ (v2 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkAnd (L.mk (L.orK w__3 a) t__4) v2)
    (a) := by
  kanon_bool

theorem Bool.and_.r_or_.swap2 :
    ∀ (v1 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkAnd v1 (L.mk (L.orK a w__3) t__4))
    (a) := by
  kanon_bool

theorem Bool.and_.r_or_.swap1_swap2 :
    ∀ (v1 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkAnd v1 (L.mk (L.orK w__3 a) t__4))
    (a) := by
  kanon_bool

theorem Bool.and_.r_eq_neq.main :
    ∀ (a : S.Term) (x : S.Term) (t__4 : S.Ty) (kanon__7 : S.Term) (y : S.Term) (t__9 : S.Ty),
    ((decide (a = kanon__7)) && (L.sure_neq x y)) = true →
    S.Refines (L.mkAnd (L.mk (L.eqK a x) t__4) (L.mk (L.eqK kanon__7 y) t__9))
    (L.vfalse) := by
  intro a x t1 b y t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inl ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) h2

theorem Bool.and_.r_eq_neq.swap2 :
    ∀ (a : S.Term) (x : S.Term) (t__4 : S.Ty) (y : S.Term) (kanon__7 : S.Term) (t__9 : S.Ty),
    ((decide (a = kanon__7)) && (L.sure_neq x y)) = true →
    S.Refines (L.mkAnd (L.mk (L.eqK a x) t__4) (L.mk (L.eqK y kanon__7) t__9))
    (L.vfalse) := by
  intro a x t1 b y t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inl ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) h2

theorem Bool.and_.r_eq_neq.swap1 :
    ∀ (x : S.Term) (a : S.Term) (t__4 : S.Ty) (kanon__7 : S.Term) (y : S.Term) (t__9 : S.Ty),
    ((decide (a = kanon__7)) && (L.sure_neq x y)) = true →
    S.Refines (L.mkAnd (L.mk (L.eqK x a) t__4) (L.mk (L.eqK kanon__7 y) t__9))
    (L.vfalse) := by
  intro a x t1 b y t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inr ⟨rfl, rfl⟩) (.inl ⟨rfl, rfl⟩) h2

theorem Bool.and_.r_eq_neq.swap1_swap2 :
    ∀ (x : S.Term) (a : S.Term) (t__4 : S.Ty) (y : S.Term) (kanon__7 : S.Term) (t__9 : S.Ty),
    ((decide (a = kanon__7)) && (L.sure_neq x y)) = true →
    S.Refines (L.mkAnd (L.mk (L.eqK x a) t__4) (L.mk (L.eqK y kanon__7) t__9))
    (L.vfalse) := by
  intro a x t1 b y t2 h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases of_decide_eq_true h1
  exact refines_and_eq_neq (.inr ⟨rfl, rfl⟩) (.inr ⟨rfl, rfl⟩) h2

theorem Bool.and_.r_default.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    S.Refines (L.mkAnd v1 v2)
    ((L.mk (if B.tag_le v1 v2 then L.andK v1 v2 else L.andK v2 v1) L.tbool)) := by
  kanon_bool

theorem Bool.or_.r_same.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    (decide (v1 = v2)) = true →
    S.Refines (L.mkOr v1 v2)
    (v1) := by
  kanon_bool

theorem Bool.or_.r_true_.main :
    ∀ (v2 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkOr (L.mk (L.litK true) t__2) v2)
    (L.vtrue) := by
  kanon_bool

theorem Bool.or_.r_true_.swap :
    ∀ (v1 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkOr v1 (L.mk (L.litK true) t__2))
    (L.vtrue) := by
  kanon_bool

theorem Bool.or_.r_false_.main :
    ∀ (v2 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkOr (L.mk (L.litK false) t__2) v2)
    (v2) := by
  kanon_bool

theorem Bool.or_.r_false_.swap :
    ∀ (v1 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkOr v1 (L.mk (L.litK false) t__2))
    (v1) := by
  kanon_bool

theorem Bool.or_.r_not.main :
    ∀ (v1 : S.Term) (kanon__3 : S.Term) (t__4 : S.Ty),
    (decide (v1 = kanon__3)) = true →
    S.Refines (L.mkOr v1 (L.mk (L.notK kanon__3) t__4))
    (L.vtrue) := by
  kanon_bool

theorem Bool.or_.r_not.swap :
    ∀ (v2 : S.Term) (kanon__3 : S.Term) (t__4 : S.Ty),
    (decide (v2 = kanon__3)) = true →
    S.Refines (L.mkOr (L.mk (L.notK kanon__3) t__4) v2)
    (L.vtrue) := by
  kanon_bool

theorem Bool.or_.r_or_.main :
    ∀ (v2 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkOr (L.mk (L.orK a w__3) t__4) v2)
    ((L.mk (L.orK a w__3) t__4)) := by
  kanon_bool

theorem Bool.or_.r_or_.swap1 :
    ∀ (v2 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkOr (L.mk (L.orK w__3 a) t__4) v2)
    ((L.mk (L.orK w__3 a) t__4)) := by
  kanon_bool

theorem Bool.or_.r_or_.swap2 :
    ∀ (v1 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkOr v1 (L.mk (L.orK a w__3) t__4))
    ((L.mk (L.orK a w__3) t__4)) := by
  kanon_bool

theorem Bool.or_.r_or_.swap1_swap2 :
    ∀ (v1 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkOr v1 (L.mk (L.orK w__3 a) t__4))
    ((L.mk (L.orK w__3 a) t__4)) := by
  kanon_bool

theorem Bool.or_.r_and_.main :
    ∀ (v2 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkOr (L.mk (L.andK a w__3) t__4) v2)
    (a) := by
  kanon_bool

theorem Bool.or_.r_and_.swap1 :
    ∀ (v2 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v2)) = true →
    S.Refines (L.mkOr (L.mk (L.andK w__3 a) t__4) v2)
    (a) := by
  kanon_bool

theorem Bool.or_.r_and_.swap2 :
    ∀ (v1 : S.Term) (a : S.Term) (w__3 : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkOr v1 (L.mk (L.andK a w__3) t__4))
    (a) := by
  kanon_bool

theorem Bool.or_.r_and_.swap1_swap2 :
    ∀ (v1 : S.Term) (w__3 : S.Term) (a : S.Term) (t__4 : S.Ty),
    (decide (a = v1)) = true →
    S.Refines (L.mkOr v1 (L.mk (L.andK w__3 a) t__4))
    (a) := by
  kanon_bool

theorem Bool.or_.r_default.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    S.Refines (L.mkOr v1 v2)
    ((L.mk (if B.tag_le v1 v2 then L.orK v1 v2 else L.orK v2 v1) L.tbool)) := by
  kanon_bool

theorem Bool.not_.r_true_.main :
    ∀ (t__2 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.litK true) t__2))
    (L.vfalse) := by
  kanon_bool

theorem Bool.not_.r_false_.main :
    ∀ (t__2 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.litK false) t__2))
    (L.vtrue) := by
  kanon_bool

theorem Bool.not_.r_not.main :
    ∀ (sv : S.Term) (t__3 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.notK sv) t__3))
    (sv) := by
  kanon_bool

theorem Bool.not_.r_or_.main :
    ∀ (v1 : S.Term) (v2 : S.Term) (t__4 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.orK v1 v2) t__4))
    ((B.b_and (B.b_not v1) (B.b_not v2))) := by
  kanon_bool

theorem Bool.not_.r_and_.main :
    ∀ (v1 : S.Term) (v2 : S.Term) (t__4 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.andK v1 v2) t__4))
    ((B.b_or (B.b_not v1) (B.b_not v2))) := by
  kanon_bool

theorem Bool.not_.r_ite.main :
    ∀ (g : S.Term) (a : S.Term) (b : S.Term) (t__4 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.iteK g a b) t__4))
    ((B.b_ite g (B.b_not a) (B.b_not b))) := by
  kanon_bool

theorem Bool.not_.r_distinct.main :
    ∀ (l : S.Term) (r : S.Term) (t__7 : S.Ty),
    S.Refines (L.mkNot (L.mk (L.distinctK (l :: (r :: []))) t__7))
    ((B.sem_eq l r)) := by
  kanon_bool

theorem Bool.not_.r_default.main :
    ∀ (sv : S.Term),
    S.Refines (L.mkNot sv)
    ((L.mk (L.notK sv) L.tbool)) := by
  kanon_bool

theorem Bool.ite.r_true_.main :
    ∀ (if_ : S.Term) (else_ : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkIte (L.mk (L.litK true) t__2) if_ else_)
    (if_) := by
  kanon_bool

theorem Bool.ite.r_false_.main :
    ∀ (if_ : S.Term) (else_ : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkIte (L.mk (L.litK false) t__2) if_ else_)
    (else_) := by
  kanon_bool

theorem Bool.ite.r_bool.main :
    ∀ (guard : S.Term) (t__3 : S.Ty) (t__5 : S.Ty),
    S.Refines (L.mkIte guard (L.mk (L.litK true) t__3) (L.mk (L.litK false) t__5))
    (guard) := by
  kanon_bool

theorem Bool.ite.r_not_bool.main :
    ∀ (guard : S.Term) (t__3 : S.Ty) (t__5 : S.Ty),
    S.Refines (L.mkIte guard (L.mk (L.litK false) t__3) (L.mk (L.litK true) t__5))
    ((B.b_not guard)) := by
  kanon_bool

theorem Bool.ite.r_false_then.main :
    ∀ (guard : S.Term) (else_ : S.Term) (t__3 : S.Ty),
    S.Refines (L.mkIte guard (L.mk (L.litK false) t__3) else_)
    ((B.b_and (B.b_not guard) else_)) := by
  kanon_bool

theorem Bool.ite.r_true_then.main :
    ∀ (guard : S.Term) (else_ : S.Term) (t__3 : S.Ty),
    S.Refines (L.mkIte guard (L.mk (L.litK true) t__3) else_)
    ((B.b_or guard else_)) := by
  kanon_bool

theorem Bool.ite.r_false_else.main :
    ∀ (guard : S.Term) (if_ : S.Term) (t__4 : S.Ty),
    S.Refines (L.mkIte guard if_ (L.mk (L.litK false) t__4))
    ((B.b_and guard if_)) := by
  kanon_bool

theorem Bool.ite.r_true_else.main :
    ∀ (guard : S.Term) (if_ : S.Term) (t__4 : S.Ty),
    S.Refines (L.mkIte guard if_ (L.mk (L.litK true) t__4))
    ((B.b_or (B.b_not guard) if_)) := by
  kanon_bool

theorem Bool.ite.r_not_guard.main :
    ∀ (if_ : S.Term) (else_ : S.Term) (g : S.Term) (t__3 : S.Ty),
    S.Refines (L.mkIte (L.mk (L.notK g) t__3) if_ else_)
    ((B.b_ite g else_ if_)) := by
  kanon_bool

theorem Bool.ite.r_guard_then.main :
    ∀ (guard : S.Term) (if_ : S.Term) (else_ : S.Term),
    (decide (guard = if_)) = true →
    S.Refines (L.mkIte guard if_ else_)
    ((B.b_or guard else_)) := by
  kanon_bool

theorem Bool.ite.r_guard_else.main :
    ∀ (guard : S.Term) (if_ : S.Term) (else_ : S.Term),
    (decide (guard = else_)) = true →
    S.Refines (L.mkIte guard if_ else_)
    ((B.b_and guard if_)) := by
  kanon_bool

theorem Bool.ite.r_ite_then.main :
    ∀ (guard : S.Term) (else_ : S.Term) (kanon__2 : S.Term) (x : S.Term) (w__4 : S.Term) (t__5 : S.Ty),
    (decide (guard = kanon__2)) = true →
    S.Refines (L.mkIte guard (L.mk (L.iteK kanon__2 x w__4) t__5) else_)
    ((B.b_ite guard x else_)) := by
  kanon_bool

theorem Bool.ite.r_ite_else.main :
    ∀ (guard : S.Term) (if_ : S.Term) (kanon__3 : S.Term) (w__4 : S.Term) (y : S.Term) (t__6 : S.Ty),
    (decide (guard = kanon__3)) = true →
    S.Refines (L.mkIte guard if_ (L.mk (L.iteK kanon__3 w__4 y) t__6))
    ((B.b_ite guard if_ y)) := by
  kanon_bool

theorem Bool.ite.r_and_ite_then.main :
    ∀ (else_ : S.Term) (g : S.Term) (w__3 : S.Term) (t__4 : S.Ty) (kanon__6 : S.Term) (x : S.Term) (w__8 : S.Term) (t__9 : S.Ty),
    (decide (g = kanon__6)) = true →
    S.Refines (L.mkIte (L.mk (L.andK g w__3) t__4) (L.mk (L.iteK kanon__6 x w__8) t__9) else_)
    ((B.b_ite (L.mk (L.andK g w__3) t__4) x else_)) := by
  kanon_bool

theorem Bool.ite.r_and_ite_then.swap :
    ∀ (else_ : S.Term) (w__3 : S.Term) (g : S.Term) (t__4 : S.Ty) (kanon__6 : S.Term) (x : S.Term) (w__8 : S.Term) (t__9 : S.Ty),
    (decide (g = kanon__6)) = true →
    S.Refines (L.mkIte (L.mk (L.andK w__3 g) t__4) (L.mk (L.iteK kanon__6 x w__8) t__9) else_)
    ((B.b_ite (L.mk (L.andK w__3 g) t__4) x else_)) := by
  kanon_bool

theorem Bool.ite.r_or_ite_else.main :
    ∀ (if_ : S.Term) (g : S.Term) (w__3 : S.Term) (t__4 : S.Ty) (kanon__7 : S.Term) (w__8 : S.Term) (y : S.Term) (t__10 : S.Ty),
    (decide (g = kanon__7)) = true →
    S.Refines (L.mkIte (L.mk (L.orK g w__3) t__4) if_ (L.mk (L.iteK kanon__7 w__8 y) t__10))
    ((B.b_ite (L.mk (L.orK g w__3) t__4) if_ y)) := by
  kanon_bool

theorem Bool.ite.r_or_ite_else.swap :
    ∀ (if_ : S.Term) (w__3 : S.Term) (g : S.Term) (t__4 : S.Ty) (kanon__7 : S.Term) (w__8 : S.Term) (y : S.Term) (t__10 : S.Ty),
    (decide (g = kanon__7)) = true →
    S.Refines (L.mkIte (L.mk (L.orK w__3 g) t__4) if_ (L.mk (L.iteK kanon__7 w__8 y) t__10))
    ((B.b_ite (L.mk (L.orK w__3 g) t__4) if_ y)) := by
  kanon_bool

theorem Bool.ite.r_same.main :
    ∀ (guard : S.Term) (if_ : S.Term) (else_ : S.Term),
    (decide (if_ = else_)) = true →
    S.Refines (L.mkIte guard if_ else_)
    (if_) := by
  kanon_bool

theorem Bool.ite.r_default.main :
    ∀ (guard : S.Term) (if_ : S.Term) (else_ : S.Term),
    S.Refines (L.mkIte guard if_ else_)
    ((L.mk (L.iteK guard if_ else_) (S.ty if_))) := by
  kanon_bool

theorem Bool.eq.r_same.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    (decide (v1 = v2)) = true →
    S.Refines (L.mkEq v1 v2)
    (L.vtrue) := by
  kanon_bool

theorem Bool.eq.r_bools.main :
    ∀ (b1 : Bool) (t__2 : S.Ty) (b2 : Bool) (t__4 : S.Ty),
    S.Refines (L.mkEq (L.mk (L.litK b1) t__2) (L.mk (L.litK b2) t__4))
    ((L.of_bool (decide (b1 = b2)))) := by
  kanon_bool

theorem Bool.eq.r_ite_ite.main :
    ∀ (b : S.Term) (l : S.Term) (r : S.Term) (t__4 : S.Ty) (kanon__5 : S.Term) (l' : S.Term) (r' : S.Term) (t__8 : S.Ty),
    (decide (b = kanon__5)) = true →
    S.Refines (L.mkEq (L.mk (L.iteK b l r) t__4) (L.mk (L.iteK kanon__5 l' r') t__8))
    ((B.b_ite b (B.sem_eq l l') (B.sem_eq r r'))) := by
  kanon_bool

theorem Bool.eq.r_false_.main :
    ∀ (v2 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkEq (L.mk (L.litK false) t__2) v2)
    ((B.b_not v2)) := by
  kanon_bool

theorem Bool.eq.r_false_.swap :
    ∀ (v1 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkEq v1 (L.mk (L.litK false) t__2))
    ((B.b_not v1)) := by
  kanon_bool

theorem Bool.eq.r_true_.main :
    ∀ (v2 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkEq (L.mk (L.litK true) t__2) v2)
    (v2) := by
  kanon_bool

theorem Bool.eq.r_true_.swap :
    ∀ (v1 : S.Term) (t__2 : S.Ty),
    S.Refines (L.mkEq v1 (L.mk (L.litK true) t__2))
    (v1) := by
  kanon_bool

theorem Bool.eq.r_nots.main :
    ∀ (b : S.Term) (t__3 : S.Ty) (c : S.Term) (t__6 : S.Ty),
    S.Refines (L.mkEq (L.mk (L.notK b) t__3) (L.mk (L.notK c) t__6))
    ((B.sem_eq b c)) := by
  kanon_bool

theorem Bool.eq.r_default.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    S.Refines (L.mkEq v1 v2)
    ((L.mk (if B.tag_le v1 v2 then L.eqK v1 v2 else L.eqK v2 v1) L.tbool)) := by
  kanon_bool

theorem Bool.eq_untyped.r_ill_typed.main [DecidableEq S.Ty] :
    ∀ (v1 : S.Term) (v2 : S.Term),
    (! (decide ((S.ty v1) = (S.ty v2)))) = true →
    S.Refines (L.mkEq v1 v2)
    (L.vfalse) := by
  kanon_bool

theorem Bool.eq_untyped.r_typed.main :
    ∀ (v1 : S.Term) (v2 : S.Term),
    S.Refines (L.mkEq v1 v2)
    ((B.sem_eq v1 v2)) := by
  kanon_bool

theorem Bool.distinct.r_small.main :
    ∀ (l : List S.Term),
    (B.at_most_one l) = true →
    S.Refines (L.mkDistinct l)
    (L.vtrue) := by
  intro l h
  match l, h with
  | [], _ | [_], _ => kanon_bool
  | _ :: _ :: _, h => rw [hB.at_most_one] at h; cases h

theorem Bool.distinct.r_distinct.main :
    ∀ (l : List S.Term),
    (decide ((B.distinct_check l) = (some true))) = true →
    S.Refines (L.mkDistinct l)
    (L.vtrue) := by
  intro l h
  simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [L.WT_lit, L.ty_mk]
  obtain ⟨hall, rfl⟩ := ev_distinct_eq_some e
  rw [Lang.WT_distinct] at w
  obtain ⟨-, E, hE⟩ := w
  have : (l.map fun x => (S.ev ρ x).getD (L.vbool false)).Nodup := by
    refine List.pairwise_map.2 ((distinct_check_true hB h).imp_of_mem fun {a b} ha hb hs he => ?_)
    obtain ⟨u, hu⟩ := hall a ha
    obtain ⟨u', hu'⟩ := hall b hb
    rw [hu, hu'] at he; simp only [Option.getD_some] at he; subst he
    exact L.sure_neq_sound ρ a b u hs ((hE a ha).1.trans (hE b hb).1.symm) (hE a ha).2
      (hE b hb).2 hu hu'
  simp [L.ev_lit, this]

theorem Bool.distinct.r_not_distinct.main :
    ∀ (l : List S.Term),
    (decide ((B.distinct_check l) = (some false))) = true →
    S.Refines (L.mkDistinct l)
    (L.vfalse) := by
  intro l h
  simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [L.WT_lit, L.ty_mk]
  obtain ⟨-, rfl⟩ := ev_distinct_eq_some e
  have : ¬ (l.map fun x => (S.ev ρ x).getD (L.vbool false)).Nodup :=
    fun h' => distinct_check_false hB h (List.Pairwise.of_map _ (fun _ _ hne he => hne (he ▸ rfl)) h')
  simp [L.ev_lit, this]

theorem Bool.distinct.r_default.main :
    ∀ (l : List S.Term),
    S.Refines (L.mkDistinct l)
    ((L.mk (L.distinctK (B.sort_by_tag l)) L.tbool)) := by
  intro l
  have hp := hB.sort_by_tag l
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · rw [Lang.WT_distinct] at w ⊢
    obtain ⟨h, E, hE⟩ := w
    exact ⟨⟨h, E, fun x hx => hE x (hp.mem_iff.1 hx)⟩, by rw [L.ty_mk, L.ty_mk]⟩
  · obtain ⟨hall, rfl⟩ := ev_distinct_eq_some e
    rw [ev_distinct fun x hx => hall x (hp.mem_iff.1 hx)]
    simp [(hp.map _).nodup_iff]

end Kanon.BoolMod
