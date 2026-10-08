import PackMod.Generated.Node
import KanonBool.Sem

/-!
# The meaning of the nodes of the pack module

A pack is the list of the values of its terms (`PackMod.Values`), wherever it
holds them (`packed`: a list, an array, an option or a record). A quantifier
`Some_ bs body` is whether some environment that gives the names `bs` values of
their sorts (`Values.Extends`) makes its body true: its meaning evaluates its
body in other environments than its own, and is poison unless the body is a
boolean in all of them. The invariants of the nodes are part of their typing,
and are stated as it is, over the sorts of the modules in a language and the
types of the children: the terms of a pack have the sort of its elements, and
the body of a quantifier is a boolean.
-/

noncomputable section

namespace PackMod

open Classical Kanon
open Kanon.Sem (OLe FLe)

/-- What the pack module needs of the values of a language: its packs, and the
environments that give names values of their sorts. -/
class Values (D : Kanon.Dom) where
  vpack : Embed (List D.Val) D.Val
  Extends : D.Env → D.Env → List (String × D.Ty) → Prop
  extends_nil : ∀ ρ' ρ, Extends ρ' ρ [] ↔ ρ' = ρ

/-- The terms of a pack, wherever it holds them; `none` for a quantifier. -/
@[kanon_wt] def packed {Ty T : Type} : Node Ty T → Option (List T)
  | .Pack l => some l
  | .Arr a => some (Node.shape2.flat a)
  | .Opt o => some (Node.shape4.flat o)
  | .Two p => some (Two.flat p)
  | .Some_ _ _ => none

/-- The terms `l` of a pack of sort `t` have the sort of its elements. -/
@[kanon_wt] def packs_wt {T Ty : Type} (sPack : Srt Ty → Ty) (ty : T → Ty) (l : List T)
    (t : Ty) : Prop :=
  ∃ e, t = sPack (.TPack e) ∧ ∀ x ∈ l, ty x = e

/-- The invariant of packs: their terms have the sort of their elements. -/
@[kanon_wt] def pack_wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sPack : Srt Ty → Ty)
    (ty : T → Ty) : Node Ty T → Ty → Prop
  | .Pack l, t => packs_wt sPack ty l t
  | .Arr a, t => packs_wt sPack ty (Node.shape2.flat a) t
  | .Opt o, t => packs_wt sPack ty (Node.shape4.flat o) t
  | .Two p, t => packs_wt sPack ty (Two.flat p) t
  | .Some_ _ _, _ => True

/-- The invariant of quantifiers: their names are distinct, and their body is a
boolean. -/
@[kanon_wt] def some_wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sPack : Srt Ty → Ty)
    (ty : T → Ty) : Node Ty T → Ty → Prop
  | .Some_ bs body, _ => (bs.map Prod.fst).Nodup ∧ ty body = sBool .TBool
  | _, _ => True

section
variable {D : Kanon.Dom} [KanonBool.Values D] [Values D]

/-- A pack of the values of terms, given in every environment. -/
def packV (ρ : D.Env) (l : List (D.Env → Option D.Val)) : Option D.Val :=
  ((l.map fun (a : D.Env → Option D.Val) => a ρ).mapM id).map Values.vpack.inj

theorem packV_mono {ρ : D.Env} {l l' : List (D.Env → Option D.Val)} (h : Forall₂ FLe l l') :
    OLe (packV ρ l) (packV ρ l') := by
  intro v e
  unfold packV at e ⊢
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.1 e
  rw [Sem.FLe.mapM h ρ vs hvs]; rfl

/-- `Some_ bs body`, given the values of `body` in every environment. -/
def someV (ρ : D.Env) (bs : List (String × D.Ty)) (body : D.Env → Option D.Val) :
    Option D.Val :=
  if ∀ ρ', Values.Extends ρ' ρ bs → ∃ b, body ρ' = some (KanonBool.Values.vbool.inj b) then
    some (KanonBool.Values.vbool.inj
      (decide (∃ ρ', Values.Extends ρ' ρ bs ∧
        body ρ' = some (KanonBool.Values.vbool.inj true))))
  else none

theorem someV_mono {ρ : D.Env} {bs : List (String × D.Ty)} {a a' : D.Env → Option D.Val}
    (h : FLe a a') : OLe (someV ρ bs a) (someV ρ bs a') := by
  intro v e
  unfold someV at e ⊢
  split at e
  · rename_i hb
    have hb' : ∀ ρ', Values.Extends ρ' ρ bs →
        ∃ b, a' ρ' = some (KanonBool.Values.vbool.inj b) := fun ρ' he => by
      obtain ⟨b, hb⟩ := hb ρ' he; exact ⟨b, h ρ' _ hb⟩
    rw [if_pos hb']
    cases e
    congr 3
    apply propext
    constructor
    · rintro ⟨ρ', he, h'⟩
      refine ⟨ρ', he, ?_⟩
      obtain ⟨b, hb⟩ := hb ρ' he
      rw [h ρ' _ hb] at h'; rw [hb, h']
    · rintro ⟨ρ', he, h'⟩; exact ⟨ρ', he, h ρ' _ h'⟩
  · cases e
end

/-- Two quantifiers have the same value when their environments correspond, with
the same values of their bodies. -/
theorem someV_congr {D : Kanon.Dom} [KanonBool.Values D] [Values D] {ρ ρ' : D.Env}
    {bs bs' : List (String × D.Ty)} {a a' : D.Env → Option D.Val}
    (h1 : ∀ ρ1, Values.Extends ρ1 ρ bs → ∃ ρ2, Values.Extends ρ2 ρ' bs' ∧ a ρ1 = a' ρ2)
    (h2 : ∀ ρ2, Values.Extends ρ2 ρ' bs' → ∃ ρ1, Values.Extends ρ1 ρ bs ∧ a ρ1 = a' ρ2) :
    someV ρ bs a = someV ρ' bs' a' := by
  have hc : (∀ ρ1, Values.Extends ρ1 ρ bs → ∃ b, a ρ1 = some (KanonBool.Values.vbool.inj b)) ↔
      (∀ ρ2, Values.Extends ρ2 ρ' bs' → ∃ b, a' ρ2 = some (KanonBool.Values.vbool.inj b)) := by
    constructor
    · intro h ρ2 e2; obtain ⟨ρ1, e1, eq⟩ := h2 ρ2 e2; rw [← eq]; exact h ρ1 e1
    · intro h ρ1 e1; obtain ⟨ρ2, e2, eq⟩ := h1 ρ1 e1; rw [eq]; exact h ρ2 e2
  have he : (∃ ρ1, Values.Extends ρ1 ρ bs ∧ a ρ1 = some (KanonBool.Values.vbool.inj true)) ↔
      (∃ ρ2, Values.Extends ρ2 ρ' bs' ∧ a' ρ2 = some (KanonBool.Values.vbool.inj true)) := by
    constructor
    · rintro ⟨ρ1, e1, h⟩; obtain ⟨ρ2, e2, eq⟩ := h1 ρ1 e1; exact ⟨ρ2, e2, eq ▸ h⟩
    · rintro ⟨ρ2, e2, h⟩; obtain ⟨ρ1, e1, eq⟩ := h2 ρ2 e2; exact ⟨ρ1, e1, eq ▸ h⟩
  unfold someV
  simp only [hc, he]

/-- The evaluation of a node in the environment `ρ`, given the values of its
children in every environment. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty) :
    Node D.Ty (D.Env → Option D.Val) → Option D.Val
  | .Pack l => packV ρ l
  | .Arr a => packV ρ (Node.shape2.flat a)
  | .Opt o => packV ρ (Node.shape4.flat o)
  | .Two p => packV ρ (Two.flat p)
  | .Some_ bs body => someV ρ bs body

theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node D.Ty (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · exact packV_mono h
  · exact packV_mono h.2
  · exact packV_mono h.2
  · exact packV_mono h.2
  · obtain ⟨rfl, h⟩ := h; exact someV_mono h

/-- The values of the sorts of the module: packs. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt D.Ty → D.Val → Prop
  | .TPack _, v => ∃ vs, v = Values.vpack.inj vs

end PackMod
