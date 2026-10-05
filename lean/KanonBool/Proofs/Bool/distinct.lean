import KanonBool.Statements.Bool.distinct
import KanonBool.Lib.Rule

/-! The arms of `Bool.distinct`, which depend on the helpers `at_most_one`,
`distinct_check_one` and `distinct_check` and on the oracle `sort_by_tag`. -/

namespace KanonBool

open Classical Kanon

set_option linter.unusedSectionVars false

section
variable {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {L : Syntax S} [Sem L]

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

theorem distinct_check_one_nil (a : S.Term) : L.bool_distinct_check_one a [] = some true := by
  rw [L.bool_distinct_check_one_eq]; rfl

theorem distinct_check_one_cons (a b : S.Term) (l : List S.Term) :
    L.bool_distinct_check_one a (b :: l) =
      if decide (a = b) then some false
      else if L.bool_sure_neq a b then L.bool_distinct_check_one a l else none := by
  rw [L.bool_distinct_check_one_eq]; rfl

theorem distinct_check_nil : L.bool_distinct_check [] = some true := by
  rw [L.bool_distinct_check_eq]; rfl

theorem distinct_check_cons (a : S.Term) (l : List S.Term) :
    L.bool_distinct_check (a :: l) =
      if L.bool_distinct_check_one a l = some true then L.bool_distinct_check l
      else L.bool_distinct_check_one a l := by
  rw [L.bool_distinct_check_eq]
  simp only [firstSome]
  split <;> simp_all

theorem distinct_check_one_true {a : S.Term} : ∀ {rest : List S.Term},
    L.bool_distinct_check_one a rest = some true → ∀ b ∈ rest, L.bool_sure_neq a b = true
  | [], _ => by simp
  | b :: rest, h => by
    rw [distinct_check_one_cons] at h
    split at h
    · cases h
    split at h
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · assumption
      · exact distinct_check_one_true h c hc
    · cases h

theorem distinct_check_one_false {a : S.Term} : ∀ {rest : List S.Term},
    L.bool_distinct_check_one a rest = some false → a ∈ rest
  | [], h => by rw [distinct_check_one_nil] at h; cases h
  | b :: rest, h => by
    rw [distinct_check_one_cons] at h
    split at h
    · rename_i he; rw [of_decide_eq_true he]; exact List.mem_cons_self
    split at h
    · exact List.mem_cons_of_mem _ (distinct_check_one_false h)
    · cases h

theorem distinct_check_true : ∀ {l : List S.Term},
    L.bool_distinct_check l = some true → l.Pairwise (fun a b => L.bool_sure_neq a b = true)
  | [], _ => .nil
  | a :: rest, h => by
    rw [distinct_check_cons] at h
    split at h
    · exact .cons (distinct_check_one_true ‹_›) (distinct_check_true h)
    · exact absurd h ‹_›

theorem distinct_check_false : ∀ {l : List S.Term},
    L.bool_distinct_check l = some false → ¬ l.Nodup
  | [], h => by rw [distinct_check_nil] at h; cases h
  | a :: rest, h => by
    rw [distinct_check_cons] at h
    rw [List.nodup_cons]
    split at h
    · exact fun h' => distinct_check_false h h'.2
    · exact fun h' => h'.1 (distinct_check_one_false h)

/-- The value of a `Distinct` that is not poison: its operands are not poison,
and it says whether their values are pairwise different. -/
theorem ev_distinct_eq_some {ρ : S.Env} {l : List S.Term} {t : S.Ty} {v : S.Val}
    (e : S.ev ρ (L.node (L.DistinctK l) t) = some v) :
    (∀ x ∈ l, ∃ u, S.ev ρ x = some u) ∧
      v = Sem.vbool L (decide (l.map fun x => (S.ev ρ x).getD (Sem.vbool L false)).Nodup) := by
  rw [Sem.ev_Distinct, pdistinct, Option.map_eq_some_iff] at e
  obtain ⟨vs, hvs, rfl⟩ := e
  obtain ⟨h, rfl⟩ := (mapM_eq_some (d := Sem.vbool L false)).1 hvs
  exact ⟨h, rfl⟩

theorem ev_distinct {ρ : S.Env} {l : List S.Term} {t : S.Ty}
    (h : ∀ x ∈ l, ∃ u, S.ev ρ x = some u) :
    S.ev ρ (L.node (L.DistinctK l) t) =
      some (Sem.vbool L (decide (l.map fun x => (S.ev ρ x).getD (Sem.vbool L false)).Nodup)) := by
  rw [Sem.ev_Distinct, (mapM_eq_some (d := Sem.vbool L false)).2 ⟨h, rfl⟩]; rfl

end

@[kanon_arm] theorem Bool.distinct.r_small.main.proof : Bool.distinct.r_small.main.Stmt := by
  intro S _ _ L _ O hO l h
  rw [L.bool_at_most_one_eq] at h
  match l, h with
  | [], _ | [_], _ => simp only [kanon_spec]; kanon_bool_sem
  | _ :: _ :: _, h => cases h

@[kanon_arm] theorem Bool.distinct.r_distinct.main.proof : Bool.distinct.r_distinct.main.Stmt := by
  intro S _ _ L _ O hO l h
  simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [Bool.distinct.spec, (Sem.v_true_eq (L := L)), L.WT_Bool, L.ty_node]
  simp only [Bool.distinct.spec] at e w
  obtain ⟨hall, rfl⟩ := ev_distinct_eq_some e
  rw [L.WT_Distinct] at w
  obtain ⟨E, -, hE⟩ := w
  have : (l.map fun x => (S.ev ρ x).getD (Sem.vbool L false)).Nodup := by
    refine List.pairwise_map.2 ((distinct_check_true h).imp_of_mem fun {a b} ha hb hs he => ?_)
    obtain ⟨u, hu⟩ := hall a ha
    obtain ⟨u', hu'⟩ := hall b hb
    rw [hu, hu'] at he; simp only [Option.getD_some] at he; subst he
    exact Sem.sure_neq_sound (L := L) ρ a b u hs ((hE a ha).1.trans (hE b hb).1.symm) (hE a ha).2
      (hE b hb).2 hu hu'
  simp [(Sem.v_true_eq (L := L)), Sem.ev_Bool, this]

@[kanon_arm] theorem Bool.distinct.r_not_distinct.main.proof :
    Bool.distinct.r_not_distinct.main.Stmt := by
  intro S _ _ L _ O hO l h
  simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [Bool.distinct.spec, (Sem.v_false_eq (L := L)), L.WT_Bool, L.ty_node]
  simp only [Bool.distinct.spec] at e
  obtain ⟨-, rfl⟩ := ev_distinct_eq_some e
  have : ¬ (l.map fun x => (S.ev ρ x).getD (Sem.vbool L false)).Nodup :=
    fun h' => distinct_check_false h (List.Pairwise.of_map _ (fun _ _ hne he => hne (he ▸ rfl)) h')
  simp [(Sem.v_false_eq (L := L)), Sem.ev_Bool, this]

@[kanon_arm] theorem Bool.distinct.r_default.main.proof : Bool.distinct.r_default.main.Stmt := by
  intro S _ _ L _ O hO l
  have hp := hO.bool_orc.sort_by_tag l
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [Bool.distinct.spec] at w ⊢
    rw [L.WT_Distinct] at w ⊢
    obtain ⟨E, h, hE⟩ := w
    exact ⟨⟨E, h, fun x hx => hE x (hp.mem_iff.1 hx)⟩, by rw [L.ty_node, L.ty_node]⟩
  · simp only [Bool.distinct.spec] at e
    obtain ⟨hall, rfl⟩ := ev_distinct_eq_some e
    rw [ev_distinct fun x hx => hall x (hp.mem_iff.1 hx)]
    simp [(hp.map _).nodup_iff]

end KanonBool
