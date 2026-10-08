import Generated.L5.Syntax
import L5.Sem
import PackMod.Sem

/-!
# The values of the language

Booleans and packs, the lists of the values of their terms; an environment
gives each variable a value, or none (poison).
-/

namespace L5

open Kanon

/-- The values: booleans and packs. -/
inductive Val where
  | bool (b : Bool)
  | pack (vs : List Val)

/-- The values of a sort. -/
def Val.Of : Val → Ty → Prop
  | .bool _, t => t = .bool .TBool
  | .pack _, t => ∃ e, t = .pack (.TPack e)

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

/-- The sorts, values and environments of the language. -/
abbrev dom : Kanon.Dom := { Ty := Ty, Val := Val, Env := Env }

/-- The environments that give the names `bs` values of their sorts, and agree
with `ρ` on the other variables. -/
def Extends (ρ' ρ : Env) (bs : List (String × Ty)) : Prop :=
  (∀ x, (∀ b ∈ bs, b.1 ≠ x) → ρ' x = ρ x) ∧ ∀ b ∈ bs, ∃ v, ρ' b.1 = some v ∧ v.Of b.2

instance : KanonBool.Values dom where
  vbool := { inj := .bool, proj := fun | .bool b => some b | _ => none,
             proj_inj := fun _ => rfl,
             inj_proj := by intro v b h; cases v <;> cases h <;> rfl }

instance : PackMod.Values dom where
  vpack := { inj := .pack, proj := fun | .pack vs => some vs | _ => none,
             proj_inj := fun _ => rfl,
             inj_proj := by intro v vs h; cases v <;> cases h <;> rfl }
  Extends := Extends
  extends_nil ρ' ρ := by
    simp only [Extends, List.not_mem_nil, false_implies, implies_true, true_implies, and_true]
    exact ⟨funext, fun h _ => h ▸ rfl⟩

instance : Values dom where
  lookup ρ x := ρ x
  Of := Val.Of

end L5
