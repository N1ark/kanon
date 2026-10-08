import Generated.L5.Semantics
import PackMod.Prims

/-!
# The values of the sorts, and the free names

Well-typed terms evaluate to values of their sort (`ev_ty`), by induction on
terms, in every environment: a quantifier evaluates its body in others.

The pack module needs the language to give the names that occur free in a term
(`used_names`), and to prove that a quantifier does not depend on the others
(`PackMod.Laws`): the value of a term depends on its free names only
(`ev_local`), and every sort has values.
-/

namespace L5

open Classical Kanon

theorem ev_ty : ∀ (e : Term) (ρ : Env) (v : Val), e.WT → ev ρ e = some v → v.Of e.ty
  | .l5 (.Var x) t, ρ, v, _, h => by
    rw [ev_l5] at h
    simp only [Node.map, Node.eval, Option.bind_eq_some_iff] at h
    obtain ⟨u, -, h⟩ := h
    split at h
    · cases h; assumption
    · cases h
  | .bool (.Ite g a b) t, ρ, v, w, h => by
    rw [WT_bool] at w; rw [ev_bool] at h
    simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
    simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pite_eq_some] at h
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩
    · show v.Of t; rw [w.1.2.2]; exact ev_ty a ρ v w.2.2.1 h
    · show v.Of t; rw [w.1.2.2, ← w.1.2.1]; exact ev_ty b ρ v w.2.2.2 h
  | .bool (.Bool _) t, ρ, v, w, h | .bool (.Not _) t, ρ, v, w, h
  | .bool (.And _ _) t, ρ, v, w, h | .bool (.Or _ _) t, ρ, v, w, h
  | .bool (.Eq _ _) t, ρ, v, w, h | .bool (.Distinct _) t, ρ, v, w, h => by
    rw [WT_bool] at w; rw [ev_bool] at h
    simp only [KanonBool.Node.wt, KanonBool.Node.All] at w
    simp only [KanonBool.Node.map, KanonBool.Node.eval, KanonBool.pnot_eq_some,
      KanonBool.pand_eq_some, KanonBool.por_eq_some, KanonBool.peq_eq_some,
      KanonBool.pdistinct_eq_some, Option.some.injEq] at h
    have ht : t = .bool .TBool := by
      first | exact w.1 | exact w.1.2 | exact w.1.2.2 | (obtain ⟨_, h, -⟩ := w.1; exact h)
    subst ht
    simp only [show (KanonBool.Values.vbool (D := dom)).inj = Val.bool from rfl] at h
    obtain ⟨b, rfl⟩ : ∃ b, v = .bool b := by grind
    rfl
  | .pack (.Pack _) t, ρ, v, w, h | .pack (.Arr _) t, ρ, v, w, h
  | .pack (.Opt _) t, ρ, v, w, h | .pack (.Two _) t, ρ, v, w, h => by
    rw [WT_pack] at w; rw [ev_pack] at h
    simp only [PackMod.Node.wt, PackMod.pack_wt, PackMod.packs_wt] at w
    simp only [PackMod.Node.map, PackMod.Node.eval, PackMod.packV,
      Option.map_eq_some_iff] at h
    obtain ⟨vs, -, rfl⟩ := h
    obtain ⟨⟨e, he, -⟩, -⟩ := w
    exact ⟨e, he⟩
  | .pack (.Some_ bs body) t, ρ, v, w, h => by
    rw [WT_pack] at w; rw [ev_pack] at h
    simp only [PackMod.Node.wt] at w
    simp only [PackMod.Node.map, PackMod.Node.eval, PackMod.someV] at h
    split at h
    · cases h; show Val.Of (.bool _) t; exact w.1.1
    · cases h

instance : KanonBool.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | bool b => cases b
                · exact .inr rfl
                · exact .inl rfl
    | pack _ => obtain ⟨_, h⟩ := this; cases h

instance : PackMod.Typed sem where
  ev_sort ρ e v s w h he := by
    have := ev_ty e ρ v w he
    rw [show e.ty = _ from h] at this
    cases s; cases v with
    | pack vs => exact ⟨vs, rfl⟩
    | bool _ => cases this

/-! ## Free names -/

/-- The children of a term, but the body of a quantifier. -/
def boolKids : KanonBool.Node Term → List Term
  | .Bool _ => []
  | .Not a => [a]
  | .And a b | .Or a b | .Eq a b => [a, b]
  | .Ite g a b => [g, a, b]
  | .Distinct l => l

/-- The children of a term, but the body of a quantifier. -/
def Term.kids : Term → List Term
  | .l5 _ _ => []
  | .bool n _ => boolKids n
  | .pack n _ => (PackMod.packed n).getD []

theorem kids_size : ∀ (e : Term), ∀ c ∈ e.kids, sizeOf c < sizeOf e
  | .l5 _ _, c, h => by simp [Term.kids] at h
  | .bool n t, c, h => by
    cases n <;> simp only [Term.kids, boolKids, List.mem_cons, List.not_mem_nil, or_false] at h
    all_goals first
      | (rcases h with rfl | rfl | rfl <;> simp <;> omega)
      | (rcases h with rfl | rfl <;> simp <;> omega)
      | (subst h; simp <;> omega)
      | (have := List.sizeOf_lt_of_mem h; simp <;> omega)
  | .pack n t, c, h => by
    cases n <;> simp only [Term.kids, PackMod.packed, Option.getD_some, Option.getD_none,
      List.not_mem_nil] at h
    all_goals first
      | (have := List.sizeOf_lt_of_mem h; simp <;> omega)
      | (kanon_size_facts; simp <;> omega)

/-- The names that occur free in a term. -/
def Term.free : Term → List String
  | .l5 (.Var x) _ => [x]
  | .pack (.Some_ bs body) _ => body.free.filter (fun x => x ∉ bs.map Prod.fst)
  | e@(.bool _ _) | e@(.pack (.Pack _) _) | e@(.pack (.Arr _) _) | e@(.pack (.Opt _) _)
  | e@(.pack (.Two _) _) => e.kids.attach.flatMap fun ⟨c, _⟩ => c.free
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (simp; omega)
    | (simp only [namedPattern] at *; subst_vars; exact kids_size _ _ ‹_›)

theorem free_kid {e c : Term} {x : String} (hc : c ∈ e.kids) (hx : x ∈ c.free) :
    x ∈ e.free := by
  match e with
  | .l5 _ _ | .pack (.Some_ _ _) _ => simp [Term.kids, PackMod.packed] at hc
  | .bool _ _ | .pack (.Pack _) _ | .pack (.Arr _) _ | .pack (.Opt _) _ | .pack (.Two _) _ =>
    rw [Term.free]; simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
    exact ⟨c, hc, hx⟩

theorem free_body {bs : List (String × Ty)} {body : Term} {t : Ty} {x : String}
    (hx : x ∈ body.free) (hb : x ∉ bs.map Prod.fst) :
    x ∈ (Term.pack (.Some_ bs body) t).free := by
  rw [Term.free]; simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨hx, hb⟩

/-- The environment `ρ1` on the names `bs`, and `ρ` on the others. -/
def over (ρ1 ρ : Env) (bs : List (String × Ty)) : Env :=
  fun x => if x ∈ bs.map Prod.fst then ρ1 x else ρ x

theorem extends_over {ρ1 ρ ρ' : Env} {bs : List (String × Ty)} (h : Extends ρ1 ρ bs) :
    Extends (over ρ1 ρ' bs) ρ' bs := by
  refine ⟨fun x hx => ?_, fun b hb => ?_⟩
  · have : x ∉ bs.map Prod.fst := by simp only [List.mem_map]; rintro ⟨b, hb, rfl⟩; exact hx b hb rfl
    simp [over, this]
  · obtain ⟨v, hv, hof⟩ := h.2 b hb
    exact ⟨v, by unfold over; rw [if_pos (List.mem_map_of_mem hb)]; exact hv, hof⟩

/-- The value of a term depends on its free names only. -/
theorem ev_local (e : Term) : ∀ ρ ρ' : Env, (∀ x ∈ e.free, ρ x = ρ' x) → ev ρ e = ev ρ' e := by
  intro ρ ρ' h
  have hk : ∀ c ∈ e.kids, ev ρ c = ev ρ' c := fun c hc =>
    ev_local c ρ ρ' (fun x hx => h x (free_kid hc hx))
  match e with
  | .l5 (.Var x) t =>
    have : ρ x = ρ' x := h x (by rw [Term.free]; simp)
    rw [ev_l5, ev_l5]; simp only [Node.map, Node.eval]
    show (ρ x).bind _ = (ρ' x).bind _
    rw [this]
  | .bool n t =>
    rw [ev_bool, ev_bool]
    cases n <;> simp only [Term.kids, boolKids, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hk <;>
      simp only [KanonBool.Node.map, KanonBool.Node.eval, hk, List.map_map, Function.comp_def]
    rename_i l
    rw [List.map_congr_left hk]
  | .pack (.Some_ bs body) t =>
    have hb : ∀ ρ1 ρ1' : Env, Extends ρ1 ρ bs → (∀ x ∈ bs.map Prod.fst, ρ1 x = ρ1' x) →
        (∀ x, x ∉ bs.map Prod.fst → ρ1' x = ρ' x) → ev ρ1 body = ev ρ1' body := by
      intro ρ1 ρ1' e1 hin hout
      refine ev_local body ρ1 ρ1' (fun x hx => ?_)
      by_cases hm : x ∈ bs.map Prod.fst
      · exact hin x hm
      · rw [hout x hm, e1.1 x (fun b hb' => fun he => hm (he ▸ List.mem_map_of_mem hb'))]
        exact h x (free_body hx hm)
    rw [ev_pack, ev_pack]
    simp only [PackMod.Node.map, PackMod.Node.eval]
    apply PackMod.someV_congr
    · intro ρ1 e1
      refine ⟨over ρ1 ρ' bs, extends_over e1, hb ρ1 _ e1 (fun x hx => by simp [over, hx])
        (fun x hx => by simp [over, hx])⟩
    · intro ρ2 e2
      refine ⟨over ρ2 ρ bs, extends_over e2, ?_⟩
      have e1 : Extends (over ρ2 ρ bs) ρ bs := extends_over e2
      refine hb _ ρ2 e1 (fun x hx => by simp [over, hx]) (fun x hx => ?_)
      exact e2.1 x (fun b hb' he => hx (he ▸ List.mem_map_of_mem hb'))
  | .pack (.Pack _) t | .pack (.Arr _) t | .pack (.Opt _) t | .pack (.Two _) t =>
    rw [ev_pack, ev_pack]
    simp only [Term.kids, PackMod.packed, Option.getD_some] at hk
    simp only [PackMod.Node.map, PackMod.Node.eval, PackMod.packV, List.map_map,
      Function.comp_def, PackMod.Node.shape2.flat_map, PackMod.Node.shape4.flat_map,
      PackMod.Two.flat_map]
    rw [List.map_congr_left hk]
termination_by sizeOf e
decreasing_by
  all_goals first
    | exact kids_size _ c hc
    | (simp; omega)

/-- A value of every sort. -/
def Ty.val : Ty → Val
  | .bool _ => .bool true
  | .pack _ => .pack []

theorem Ty.val_of : ∀ t : Ty, (Ty.val t).Of t
  | .bool .TBool => rfl
  | .pack (.TPack _) => ⟨_, rfl⟩

/-- Distinct names name distinct binders. -/
theorem eq_of_nodup : ∀ {bs : List (String × Ty)}, (bs.map Prod.fst).Nodup →
    ∀ {a b}, a ∈ bs → b ∈ bs → a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | c :: bs, hn, a, b, ha, hb, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd h.symm (hn.1 b hb)
    · exact absurd h (hn.1 a ha)
    · exact eq_of_nodup hn.2 ha hb h

/-- The names of `bs` that occur free in `body`. -/
def usedNames (bs : List (String × Ty)) (body : Term) : List (String × Ty) :=
  bs.filter (fun b => b.1 ∈ body.free)

theorem mem_used {bs : List (String × Ty)} {body : Term} {x : String} (hx : x ∈ body.free)
    (hb : x ∈ bs.map Prod.fst) : x ∈ (usedNames bs body).map Prod.fst := by
  obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hb
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨hb', by simpa using hx⟩)

/-- Dropping the names that the body does not use does not change a
quantifier. -/
theorem ev_used (ρ : Env) (bs : List (String × Ty)) (body : Term) (t : Ty)
    (hn : (bs.map Prod.fst).Nodup) :
    ev ρ (.pack (.Some_ bs body) t) = ev ρ (.pack (.Some_ (usedNames bs body) body) t) := by
  have sub : ∀ b ∈ usedNames bs body, b ∈ bs := fun b hb => (List.mem_filter.1 hb).1
  rw [ev_pack, ev_pack]
  simp only [PackMod.Node.map, PackMod.Node.eval]
  apply PackMod.someV_congr
  · intro ρ1 e1
    refine ⟨over ρ1 ρ (usedNames bs body), ⟨fun x hx => ?_, fun b hb => ?_⟩, ?_⟩
    · have : x ∉ (usedNames bs body).map Prod.fst := by
        intro h; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h; exact hx b hb rfl
      simp [over, this]
    · obtain ⟨v, hv, hof⟩ := e1.2 b (sub b hb)
      exact ⟨v, by unfold over; rw [if_pos (List.mem_map_of_mem hb)]; exact hv, hof⟩
    · refine ev_local body _ _ (fun x hx => ?_)
      unfold over
      split
      · rfl
      · rename_i hu
        refine e1.1 x (fun b hb he => hu ?_)
        subst he; exact mem_used hx (List.mem_map_of_mem hb)
  · intro ρ2 e2
    let ρ1 : Env := fun x =>
      if x ∈ (usedNames bs body).map Prod.fst then ρ2 x
      else match bs.find? (fun b => b.1 = x) with
        | some b => some (Ty.val b.2)
        | none => ρ x
    refine ⟨ρ1, ⟨fun x hx => ?_, fun b hb => ?_⟩, ?_⟩
    · have hu : x ∉ (usedNames bs body).map Prod.fst := by
        intro h; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h; exact hx b (sub b hb) rfl
      have hf : bs.find? (fun b => b.1 = x) = none :=
        List.find?_eq_none.2 (fun b hb h => hx b hb (by simpa using h))
      simp only [ρ1, if_neg hu, hf]
    · by_cases hu : b.1 ∈ (usedNames bs body).map Prod.fst
      · obtain ⟨b', hb', he⟩ := List.mem_map.1 hu
        obtain ⟨v, hv, hof⟩ := e2.2 b' hb'
        have : b' = b := eq_of_nodup hn (sub b' hb') hb he
        subst this
        exact ⟨v, by simp only [ρ1, if_pos hu]; exact hv, hof⟩
      · cases hf : bs.find? (fun b' => b'.1 = b.1) with
        | none =>
          exact absurd (List.find?_eq_none.1 hf b hb) (by simp)
        | some b' =>
          have hb' := List.mem_of_find?_eq_some hf
          have he : b'.1 = b.1 := by simpa using List.find?_some hf
          have : b' = b := eq_of_nodup hn hb' hb he
          subst this
          exact ⟨Ty.val b'.2, by simp only [ρ1, if_neg hu, hf], Ty.val_of _⟩
    · refine ev_local body _ _ (fun x hx => ?_)
      simp only [ρ1]
      split
      · rfl
      · rename_i hu
        have hx' : x ∉ bs.map Prod.fst := fun h => hu (mem_used hx h)
        have hf : bs.find? (fun b => b.1 = x) = none :=
          List.find?_eq_none.2 (fun b hb h => hx' (by
            simp only [decide_eq_true_eq] at h; exact h ▸ List.mem_map_of_mem hb))
        rw [hf]
        exact (e2.1 x (fun b hb he => hu (he ▸ List.mem_map_of_mem hb))).symm

instance : PackMod.Laws sem where
  used_names := usedNames
  used_sublist _ _ := List.filter_sublist
  ev_used ρ names body t w := by
    obtain ⟨-, hn, -, -⟩ := PackMod.WT_some w
    exact ev_used ρ names body t hn

end L5
