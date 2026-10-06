import KanonBool.Statements

/-!
# The arms of the bool module that the default tactic does not prove

`a == x && a == y` is false for `x` and `y` surely different (`sure_neq`); the
arms of `Bool.distinct` depend on the helpers `at_most_one`,
`distinct_check_one` and `distinct_check`, and on the oracle `sort_by_tag`.
-/

namespace KanonBool

open Classical Kanon

set_option linter.unusedSectionVars false

section
variable {S : Kanon.Sem} [Lang S] [Typed S]

@[simp] theorem ty_v_true : S.ty (v_true (S := S)) = sort .TBool := by simp [v_true]
@[simp] theorem ty_v_false : S.ty (v_false (S := S)) = sort .TBool := by simp [v_false]
@[simp] theorem WT_v_true : S.WT (v_true (S := S)) := by simp [v_true, WT_mk, Node.wt, Node.All]
@[simp] theorem WT_v_false : S.WT (v_false (S := S)) := by
  simp [v_false, WT_mk, Node.wt, Node.All]
theorem ev_v_true (ρ : S.Env) : S.ev ρ (v_true (S := S)) = some (Values.vbool.inj true) := by
  simp [v_true, ev_mk, Node.map, Node.eval]
theorem ev_v_false (ρ : S.Env) : S.ev ρ (v_false (S := S)) = some (Values.vbool.inj false) := by
  simp [v_false, ev_mk, Node.map, Node.eval]

end

@[kanon_arm] theorem Bool.and_.r_eq_neq.main.proof : Bool.and_.r_eq_neq.main.Stmt := by
  intro S _ _ O hO a x t1 a' y t2 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl, hn⟩ := h
  have hp := hO.bool_sure_neq x y
  rw [hn] at hp
  refine Sem.Refines.intro (fun w => ⟨WT_v_false, by simp [Bool.and_.spec]⟩)
    (fun ρ v w _ e => ?_)
  simp only [Bool.and_.spec, WT_mk, Node.wt, Node.All] at w
  obtain ⟨-, ⟨⟨hx, -⟩, wa, wx⟩, ⟨hy, -⟩, -, wy⟩ := w
  simp only [Bool.and_.spec, ev_mk, Node.map, Node.eval] at e
  rw [ev_v_false]
  rw [pand_eq_some] at e
  rcases e with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨e1, e2, -⟩
  · rfl
  · rfl
  rw [peq_eq_some] at e1 e2
  obtain ⟨u1, u1', e1, e1', hu1⟩ := e1
  obtain ⟨u2, u2', e2, e2', hu2⟩ := e2
  simp only [Embed.inj_eq_iff] at hu1 hu2
  have h1 := of_decide_eq_true hu1.symm
  have h2 := of_decide_eq_true hu2.symm
  subst h1 h2
  rw [e1] at e2; cases e2
  exact (hp rfl wx wy (hx.trans hy.symm) ρ u1 e1' e2').elim

section
variable {S : Kanon.Sem} [Lang S] [Typed S] {O : Ops S}

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

theorem distinct_check_one_nil (a : S.Term) : Bool.distinct_check_one O a [] = some true := by
  rw [Bool.distinct_check_one]; rfl

theorem distinct_check_one_cons (a b : S.Term) (l : List S.Term) :
    Bool.distinct_check_one O a (b :: l) =
      if decide (a = b) then some false
      else if O.bool_sure_neq a b then Bool.distinct_check_one O a l else none := by
  rw [Bool.distinct_check_one]; rfl

theorem distinct_check_nil : Bool.distinct_check O [] = some true := by
  rw [Bool.distinct_check]; rfl

theorem distinct_check_cons (a : S.Term) (l : List S.Term) :
    Bool.distinct_check O (a :: l) =
      if Bool.distinct_check_one O a l = some true then Bool.distinct_check O l
      else Bool.distinct_check_one O a l := by
  rw [Bool.distinct_check]
  simp only [firstSome]
  split <;> simp_all

theorem distinct_check_one_true {a : S.Term} : ∀ {rest : List S.Term},
    Bool.distinct_check_one O a rest = some true → ∀ b ∈ rest, O.bool_sure_neq a b = true
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
    Bool.distinct_check_one O a rest = some false → a ∈ rest
  | [], h => by rw [distinct_check_one_nil] at h; cases h
  | b :: rest, h => by
    rw [distinct_check_one_cons] at h
    split at h
    · rename_i he; rw [of_decide_eq_true he]; exact List.mem_cons_self
    split at h
    · exact List.mem_cons_of_mem _ (distinct_check_one_false h)
    · cases h

theorem distinct_check_true : ∀ {l : List S.Term},
    Bool.distinct_check O l = some true → l.Pairwise (fun a b => O.bool_sure_neq a b = true)
  | [], _ => .nil
  | a :: rest, h => by
    rw [distinct_check_cons] at h
    split at h
    · exact .cons (distinct_check_one_true ‹_›) (distinct_check_true h)
    · exact absurd h ‹_›

theorem distinct_check_false : ∀ {l : List S.Term},
    Bool.distinct_check O l = some false → ¬ l.Nodup
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
    (e : S.ev ρ (mk (.Distinct l) t) = some v) :
    (∀ x ∈ l, ∃ u, S.ev ρ x = some u) ∧
      v = Values.vbool.inj
        (decide (l.map fun x => (S.ev ρ x).getD (Values.vbool.inj false)).Nodup) := by
  rw [ev_mk, Node.map, Node.eval, pdistinct, Option.map_eq_some_iff] at e
  obtain ⟨vs, hvs, rfl⟩ := e
  rw [List.map_map, List.mapM_map] at hvs
  change l.mapM (S.ev ρ) = some vs at hvs
  obtain ⟨h, rfl⟩ := (mapM_eq_some (d := Values.vbool.inj false)).1 hvs
  exact ⟨fun x hx => h x hx, rfl⟩

theorem ev_distinct {ρ : S.Env} {l : List S.Term} {t : S.Ty}
    (h : ∀ x ∈ l, ∃ u, S.ev ρ x = some u) :
    S.ev ρ (mk (.Distinct l) t) =
      some (Values.vbool.inj
        (decide (l.map fun x => (S.ev ρ x).getD (Values.vbool.inj false)).Nodup)) := by
  rw [ev_mk, Node.map, Node.eval, pdistinct, List.map_map, List.mapM_map]
  rw [show (id ∘ (· ρ) ∘ fun c ρ => S.ev ρ c) = S.ev ρ from rfl, (mapM_eq_some (d := Values.vbool.inj false)).2 ⟨h, rfl⟩]
  rfl

end

@[kanon_arm] theorem Bool.distinct.r_small.main.proof : Bool.distinct.r_small.main.Stmt := by
  intro S _ _ O hO l h
  simp only [Bool.at_most_one, firstSome] at h
  refine Sem.Refines.intro (fun w => ⟨WT_v_true, by simp [Bool.distinct.spec]⟩)
    (fun ρ v w _ e => ?_)
  rw [ev_v_true]
  simp only [Bool.distinct.spec] at e
  obtain ⟨-, rfl⟩ := ev_distinct_eq_some e
  match l, h with
  | [], _ | [_], _ => simp
  | _ :: _ :: _, h => simp at h

@[kanon_arm] theorem Bool.distinct.r_distinct.main.proof : Bool.distinct.r_distinct.main.Stmt := by
  intro S _ _ O hO l h
  simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ⟨WT_v_true, by simp [Bool.distinct.spec]⟩)
    (fun ρ v w _ e => ?_)
  rw [ev_v_true]
  simp only [Bool.distinct.spec] at e w
  obtain ⟨hall, rfl⟩ := ev_distinct_eq_some e
  simp only [WT_mk, Node.wt, Node.All] at w
  obtain ⟨⟨E, -, hE⟩, hw⟩ := w
  have : (l.map fun x => (S.ev ρ x).getD (Values.vbool.inj false)).Nodup := by
    refine List.pairwise_map.2 ((distinct_check_true h).imp_of_mem fun {a b} ha hb hs he => ?_)
    obtain ⟨u, hu⟩ := hall a ha
    obtain ⟨u', hu'⟩ := hall b hb
    rw [hu, hu'] at he; simp only [Option.getD_some] at he; subst he
    exact hO.bool_sure_neq a b hs (hw a ha) (hw b hb) ((hE a ha).trans (hE b hb).symm) ρ u hu hu'
  simp [this]

@[kanon_arm] theorem Bool.distinct.r_not_distinct.main.proof :
    Bool.distinct.r_not_distinct.main.Stmt := by
  intro S _ _ O hO l h
  simp only [decide_eq_true_eq] at h
  refine Sem.Refines.intro (fun w => ⟨WT_v_false, by simp [Bool.distinct.spec]⟩)
    (fun ρ v w _ e => ?_)
  rw [ev_v_false]
  simp only [Bool.distinct.spec] at e
  obtain ⟨-, rfl⟩ := ev_distinct_eq_some e
  have : ¬ (l.map fun x => (S.ev ρ x).getD (Values.vbool.inj false)).Nodup :=
    fun h' => distinct_check_false h (List.Pairwise.of_map _ (fun _ _ hne he => hne (he ▸ rfl)) h')
  simp [this]

@[kanon_arm] theorem Bool.distinct.r_default.main.proof : Bool.distinct.r_default.main.Stmt := by
  intro S _ _ O hO l
  have hp := hO.bool_orc.sort_by_tag l
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp only [Bool.distinct.spec, WT_mk, Node.wt, Node.All, ty_mk] at w ⊢
    obtain ⟨⟨E, h, hE⟩, hw⟩ := w
    exact ⟨⟨⟨E, h, fun x hx => hE x (hp.mem_iff.1 hx)⟩, fun x hx => hw x (hp.mem_iff.1 hx)⟩,
      trivial⟩
  · simp only [Bool.distinct.spec] at e
    obtain ⟨hall, rfl⟩ := ev_distinct_eq_some e
    rw [ev_distinct fun x hx => hall x (hp.mem_iff.1 hx)]
    simp [(hp.map _).nodup_iff]

end KanonBool
