import PackMod.Node
import KanonBool.Sem

/-!
# The meaning of the nodes of the pack module

A pack is the list of the values of its terms (`PackMod.Values`). A quantifier
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

/-- The invariant of packs: their terms have the sort of their elements. -/
@[kanon_wt] def pack_wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sPack : Srt Ty → Ty)
    (ty : T → Ty) : Node Ty T → Ty → Prop
  | .Pack l, t => ∃ e, t = sPack (.TPack e) ∧ ∀ x ∈ l, ty x = e
  | _, _ => True

/-- The invariant of quantifiers: their body is a boolean. -/
@[kanon_wt] def some_wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sPack : Srt Ty → Ty)
    (ty : T → Ty) : Node Ty T → Ty → Prop
  | .Some_ _ body, _ => ty body = sBool .TBool
  | _, _ => True

section
variable {D : Kanon.Dom} [KanonBool.Values D] [Values D]

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

/-- The evaluation of a node in the environment `ρ`, given the values of its
children in every environment. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty) :
    Node D.Ty (D.Env → Option D.Val) → Option D.Val
  | .Pack l => ((l.map fun (a : D.Env → Option D.Val) => a ρ).mapM id).map Values.vpack.inj
  | .Some_ bs body => someV ρ bs body

theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node D.Ty (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · intro v e
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [Sem.FLe.mapM h ρ vs hvs]; rfl
  · obtain ⟨rfl, h⟩ := h; exact someV_mono h

/-- The values of the sorts of the module: packs. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt D.Ty → D.Val → Prop
  | .TPack _, v => ∃ vs, v = Values.vpack.inj vs

end PackMod
