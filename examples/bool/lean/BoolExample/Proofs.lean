import BoolExample.Lib.Rule

/-!
# Hand-written proofs of arms

The arms of `b_distinct` reason on lists of terms, which `kanon_auto` does not
do: they are proved here, by theorems tagged `@[kanon_arm]`, which the
generated proofs use instead of `kanon_auto`.
-/

namespace BoolExample

open Kanon

/-! ## Lists of terms -/

theorem WTList_iff {e : Ty} : ∀ {l : List Term}, Term.WTList e l ↔ ∀ t ∈ l, t.WT
  | [] => by simp [Term.WTList]
  | t :: ts => by simp [Term.WTList, WTList_iff (l := ts)]

/-- The value of a term that is not poison (`false` otherwise). -/
noncomputable def evD (ρ : Env) (t : Term) : Bool := (ev ρ t).getD false

theorem evList_eq_some {ρ : Env} : ∀ {l : List Term} {vs : List Bool},
    evList ρ l = some vs ↔ (∀ t ∈ l, ∃ v, ev ρ t = some v) ∧ vs = l.map (evD ρ)
  | [], vs => by simp [evList, eq_comm]
  | t :: ts, vs => by
    simp only [evList]
    constructor
    · intro h
      split at h
      · rename_i v vs' hv hvs
        cases h
        obtain ⟨h1, h2⟩ := evList_eq_some.1 hvs
        exact ⟨fun t' ht' => (List.mem_cons.1 ht').elim (fun e => e ▸ ⟨v, hv⟩) (h1 t'),
          by simp [h2, evD, hv]⟩
      · cases h
    · rintro ⟨h1, rfl⟩
      obtain ⟨v, hv⟩ := h1 t (by simp)
      rw [hv, evList_eq_some.2 ⟨fun t' ht' => h1 t' (by simp [ht']), rfl⟩]
      simp [evD, hv]

/-- A `Distinct` that is not poison: its elements are well-typed and not poison,
and its value is whether their values are pairwise different. -/
theorem eval_distinct_eq_some {ρ : Env} {l : List Term} {v : Bool}
    (e : eval ρ (b_distinct.spec l) = some v) :
    (∀ t ∈ l, t.WT) ∧ (∀ t ∈ l, ∃ v, ev ρ t = some v) ∧ v = decide (l.map (evD ρ)).Nodup := by
  have w := eval_WT e
  rw [eval_eq_ev w] at e
  simp only [b_distinct.spec, Term.WT] at w
  obtain ⟨-, E, wl⟩ := w
  simp only [b_distinct.spec, ev, Option.map_eq_some_iff] at e
  obtain ⟨vs, hvs, rfl⟩ := e
  obtain ⟨hall, rfl⟩ := evList_eq_some.1 hvs
  exact ⟨WTList_iff.1 wl, hall, rfl⟩

theorem eval_distinct {ρ : Env} {l : List Term} (w : ∀ t ∈ l, t.WT)
    (hall : ∀ t ∈ l, ∃ v, ev ρ t = some v) :
    eval ρ (.mk (.Nop .Distinct l) .TBool) = some (decide (l.map (evD ρ)).Nodup) := by
  have w' : (Term.mk (.Nop .Distinct l) .TBool).WT := by simp_all [Term.WT, WTList_iff]
  rw [eval_eq_ev w']
  simp [ev, evList_eq_some.2 ⟨hall, rfl⟩]

theorem eval_bool {ρ : Env} {b : Bool} : eval ρ (.mk (.Bool b) .TBool) = some b := by
  simp [eval, Term.WT, ev]

/-! ## `distinct_check` -/

theorem distinct_check_one_true {a : Term} : ∀ {rest : List Term},
    distinct_check_one a rest = some true → ∀ b ∈ rest, sure_neq a b = true
  | [], _ => by simp
  | b :: rest, h => by
    rw [distinct_check_one] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    split at h
    · simp at h
    · split at h
      · rename_i hs
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hs
        · exact distinct_check_one_true h c hc
      · simp at h

theorem distinct_check_one_false {a : Term} : ∀ {rest : List Term},
    distinct_check_one a rest = some false → a ∈ rest
  | [], h => by
    rw [distinct_check_one] at h
    simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
  | b :: rest, h => by
    rw [distinct_check_one] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    split at h
    · rename_i he; simp [equal] at he; simp [he]
    · split at h
      · exact List.mem_cons_of_mem _ (distinct_check_one_false h)
      · simp at h

theorem distinct_check_true : ∀ {l : List Term},
    distinct_check l = some true → l.Pairwise (fun a b => sure_neq a b = true)
  | [], _ => by simp
  | a :: rest, h => by
    rw [distinct_check] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    cases h1 : distinct_check_one a rest with
    | none => simp [h1] at h
    | some b =>
      cases b
      · simp [h1] at h
      · simp only [h1] at h
        exact List.Pairwise.cons (distinct_check_one_true h1) (distinct_check_true h)

theorem distinct_check_false : ∀ {l : List Term}, distinct_check l = some false → ¬ l.Nodup
  | [], h => by
    rw [distinct_check] at h
    simp [firstSome, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
  | a :: rest, h => by
    rw [distinct_check] at h
    simp only [firstSome, Option.getD_some, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
    cases h1 : distinct_check_one a rest with
    | none => simp [h1] at h
    | some b =>
      cases b
      · simp [distinct_check_one_false h1]
      · simp only [h1] at h
        simp [distinct_check_false h]

/-- Terms that are surely different have different values. -/
theorem evD_ne_of_sure_neq {ρ : Env} {a b : Term} (h : sure_neq a b = true) :
    evD ρ a ≠ evD ρ b := by
  obtain ⟨x, y, t, t', rfl, rfl, hxy⟩ := sure_neq_iff.1 h
  simpa [evD, ev] using hxy

/-! ## The arms of `b_distinct` -/

@[kanon_arm] theorem b_distinct.r_small.main.proof : b_distinct.r_small.main.Stmt := by
  intro O hO l h
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [at_most_one, firstSome] at h <;>
    simp only [kanon_spec] <;> kanon_sem

@[kanon_arm] theorem b_distinct.r_distinct.main.proof : b_distinct.r_distinct.main.Stmt := by
  intro O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun ρ v e => ?_⟩
  obtain ⟨-, -, rfl⟩ := eval_distinct_eq_some e
  have : (l.map (evD ρ)).Nodup :=
    List.pairwise_map.2 ((distinct_check_true hc).imp evD_ne_of_sure_neq)
  simp [this, v_true, eval_bool]

@[kanon_arm] theorem b_distinct.r_not_distinct.main.proof :
    b_distinct.r_not_distinct.main.Stmt := by
  intro O hO l hc
  simp only [decide_eq_true_eq] at hc
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun ρ v e => ?_⟩
  obtain ⟨-, -, rfl⟩ := eval_distinct_eq_some e
  have : ¬ (l.map (evD ρ)).Nodup := fun h =>
    distinct_check_false hc (List.Pairwise.of_map _ (fun _ _ hne he => hne (he ▸ rfl)) h)
  simp [this, v_false, eval_bool]

@[kanon_arm] theorem b_distinct.r_default.main.proof : b_distinct.r_default.main.Stmt := by
  intro O hO l
  have hp := hO.orc.sort_by_tag l
  refine ⟨fun w => ⟨?_, rfl⟩, fun ρ v e => ?_⟩
  · simp_all [b_distinct.spec, Term.WT, WTList_iff, hp.mem_iff]
  · obtain ⟨w, hall, rfl⟩ := eval_distinct_eq_some e
    rw [eval_distinct (fun t ht => w t (hp.mem_iff.1 ht)) (fun t ht => hall t (hp.mem_iff.1 ht))]
    simp [(hp.map (evD ρ)).nodup_iff]

end BoolExample
