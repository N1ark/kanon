import PackMod.Statements

/-!
# The proofs of the pack module that the tactics do not find

A quantifier without names is its body, and packs of one term are different
when their terms are (by the case of `sure_neq` on the terms).
-/

namespace PackMod

open Kanon

/-- A quantifier without names, when it is not poison, is the value of its body. -/
theorem someV_nil {D : Kanon.Dom} [KanonBool.Values D] [Values D] {ρ : D.Env}
    {a : D.Env → Option D.Val} {v : D.Val} (h : someV ρ [] a = some v) :
    ∃ b, a ρ = some (KanonBool.Values.vbool.inj b) ∧ v = KanonBool.Values.vbool.inj b := by
  unfold someV at h
  split at h
  · rename_i hb
    obtain ⟨b, hb⟩ := hb ρ ((Values.extends_nil ρ ρ).2 rfl)
    cases h
    refine ⟨b, hb, ?_⟩
    cases b <;> simp [Values.extends_nil, hb]
  · cases h

@[kanon_arm] theorem Pack.some_.r_empty.main.proof : Pack.some_.r_empty.main.Stmt := by
  intro S _ _ _ _ O hO names body h
  cases names with
  | cons _ _ => simp [Pack.no_names, firstSome] at h
  | nil =>
    refine Kanon.Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
    · rw [Pack.some_.spec, WT_mk] at w
      simp only [Node.wt, some_wt, Node.All] at w
      exact ⟨w.2, by simp [Pack.some_.spec, w.1.2]⟩
    · rw [Pack.some_.spec, ev_mk] at e
      simp only [Node.map, Node.eval] at e
      obtain ⟨b, hb, rfl⟩ := someV_nil e
      exact hb

/-- A term that is a pack of one term. -/
theorem pack_one {S : Kanon.Sem} [KanonBool.Lang S] [Lang S] {a a' : S.Term}
    (h : proj a = some (.Pack [a'])) (w : S.WT a) (ρ : S.Env) {u : S.Val}
    (e : S.ev ρ a = some u) :
    S.WT a' ∧ (∃ x, S.ty a = sort (.TPack x) ∧ S.ty a' = x) ∧
      ∃ v, S.ev ρ a' = some v ∧ u = Values.vpack.inj [v] := by
  obtain ⟨t, rfl⟩ := Kanon.NodeEmbed.exists_of_proj _ h
  rw [WT_mk] at w
  simp only [Node.wt, pack_wt, Node.All, List.mem_singleton, forall_eq] at w
  obtain ⟨⟨x, hx, hty⟩, wa⟩ := w
  refine ⟨wa, ⟨x, by simpa using hx, hty⟩, ?_⟩
  rw [ev_mk] at e
  simp only [Node.map, Node.eval, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    id, Option.bind_eq_bind, Option.pure_def, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at e
  obtain ⟨_, ⟨v, hv, _, h1, h2⟩, rfl⟩ := e
  cases h1; cases h2
  exact ⟨v, hv, rfl⟩

@[kanon_arm] theorem Bool.sure_neq.c1.proof : Bool.sure_neq.c1.Stmt := by
  intro S _ _ _ _ O hO a b r h
  simp only [Bool.sure_neq.c1] at h
  split at h
  · rename_i a' b' ha hb
    cases h
    intro hr wa wb hty ρ u ea eb
    obtain ⟨wa', ⟨x, hx, hx'⟩, va, eva, rfl⟩ := pack_one ha wa ρ ea
    obtain ⟨wb', ⟨y, hy, hy'⟩, vb, evb, hu⟩ := pack_one hb wb ρ eb
    rw [hx, hy, sort_inj_iff, Srt.TPack.injEq] at hty
    simp only [Embed.inj_eq_iff, List.cons.injEq, and_true] at hu
    subst hty hu
    exact hO.bool_sure_neq a' b' hr wa' wb' (hx'.trans hy'.symm) ρ va eva evb
  · cases h

end PackMod
