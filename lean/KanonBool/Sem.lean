import Generated.KanonBool.Node
import KanonCore.Embed
import KanonCore.ProofAttr

/-!
# The meaning of the nodes of the bool module

The bool module needs the booleans among the values of a language
(`KanonBool.Values`), and evaluates its nodes by the operations below, given the
values of their children in the environment, where `none` is poison:

- `pand` and `por` are "parallel": a `false` (resp. `true`) operand wins over a
  poisoned one, as it would over any value of the unspecified one;
- `pnot` and `peq` are poison when an operand is, and `peq` compares values;
- `pite` only uses the branch it selects;
- `pdistinct` is whether the values are pairwise different.
-/

noncomputable section

namespace KanonBool

open Classical Kanon
open Kanon.Sem (OLe)

/-- What the bool module needs of the values of a language: its booleans. -/
class Values (D : Kanon.Dom) where
  vbool : Embed Bool D.Val

section
variable {V : Type} (vb : Bool → V)

/-- Parallel conjunction: `false` wins over poison. -/
def pand (a b : Option V) : Option V :=
  if a = some (vb false) ∨ b = some (vb false) then some (vb false)
  else if a = some (vb true) ∧ b = some (vb true) then some (vb true)
  else none

/-- Parallel disjunction: `true` wins over poison. -/
def por (a b : Option V) : Option V :=
  if a = some (vb true) ∨ b = some (vb true) then some (vb true)
  else if a = some (vb false) ∧ b = some (vb false) then some (vb false)
  else none

/-- Negation. -/
def pnot (a : Option V) : Option V :=
  if a = some (vb true) then some (vb false)
  else if a = some (vb false) then some (vb true)
  else none

/-- Equality of values. -/
def peq : Option V → Option V → Option V
  | some x, some y => some (vb (decide (x = y)))
  | _, _ => none

/-- The conditional, which only uses the branch it selects. -/
def pite (g a b : Option V) : Option V :=
  if g = some (vb true) then a else if g = some (vb false) then b else none

/-- `Distinct`: whether the values are pairwise different. -/
def pdistinct (vs : Option (List V)) : Option V :=
  vs.map fun vs => vb (decide vs.Nodup)
end

/-- The evaluation of a node in the environment `ρ`, given the values of its
children in every environment. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Bool b => some (Values.vbool.inj b)
  | .Not a => pnot Values.vbool.inj (a ρ)
  | .And a b => pand Values.vbool.inj (a ρ) (b ρ)
  | .Or a b => por Values.vbool.inj (a ρ) (b ρ)
  | .Eq a b => peq Values.vbool.inj (a ρ) (b ρ)
  | .Ite g a b => pite Values.vbool.inj (g ρ) (a ρ) (b ρ)
  | .Distinct l => pdistinct Values.vbool.inj ((l.map (· ρ)).mapM id)

/-- The values of the sorts of the module: `true` and `false`. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TBool, v => v = Values.vbool.inj true ∨ v = Values.vbool.inj false

/-! The operations on known values, unfolded by the closing steps. -/
attribute [kanon_close_simp] pand por pnot peq pite pdistinct

/-! ## The operations by cases -/

section
variable {V : Type} {vb : Bool → V} {a b g : Option V} {x y : V}

@[kanon_val] theorem pand_eq_some :
    pand vb a b = some x ↔
      (a = some (vb false) ∧ x = vb false) ∨ (b = some (vb false) ∧ x = vb false) ∨
        (a = some (vb true) ∧ b = some (vb true) ∧ x = vb true) := by
  unfold pand; (repeat' split) <;> grind

@[kanon_val] theorem por_eq_some :
    por vb a b = some x ↔
      (a = some (vb true) ∧ x = vb true) ∨ (b = some (vb true) ∧ x = vb true) ∨
        (a = some (vb false) ∧ b = some (vb false) ∧ x = vb false) := by
  unfold por; (repeat' split) <;> grind

@[kanon_val] theorem pnot_eq_some :
    pnot vb a = some x ↔
      (a = some (vb true) ∧ x = vb false) ∨ (a = some (vb false) ∧ x = vb true) := by
  unfold pnot; (repeat' split) <;> grind

@[kanon_val] theorem peq_eq_some :
    peq vb a b = some x ↔ ∃ u w, a = some u ∧ b = some w ∧ x = vb (decide (u = w)) := by
  unfold peq; split <;> simp_all [eq_comm]

@[kanon_val] theorem pite_eq_some :
    pite vb g a b = some x ↔ (g = some (vb true) ∧ a = some x) ∨
      (g = some (vb false) ∧ g ≠ some (vb true) ∧ b = some x) := by
  unfold pite; (repeat' split) <;> simp_all

@[kanon_val] theorem pdistinct_eq_some {vs : Option (List V)} :
    pdistinct vb vs = some x ↔ ∃ l, vs = some l ∧ x = vb (decide l.Nodup) := by
  unfold pdistinct; cases vs <;> simp [eq_comm]

end

/-! ## Monotonicity in poison -/

section
variable {V : Type} {vb : Bool → V}

theorem pand_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (pand vb a b) (pand vb a' b') := by
  intro v e
  rw [pand_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact .inl ⟨ha _ h, rfl⟩
  · exact .inr (.inl ⟨hb _ h, rfl⟩)
  · exact .inr (.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem por_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (por vb a b) (por vb a' b') := by
  intro v e
  rw [por_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact .inl ⟨ha _ h, rfl⟩
  · exact .inr (.inl ⟨hb _ h, rfl⟩)
  · exact .inr (.inr ⟨ha _ h1, hb _ h2, rfl⟩)

theorem pnot_mono {a a' : Option V} (ha : OLe a a') : OLe (pnot vb a) (pnot vb a') := by
  intro v e
  rw [pnot_eq_some] at *
  rcases e with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact .inl ⟨ha _ h, rfl⟩
  · exact .inr ⟨ha _ h, rfl⟩

theorem peq_mono {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (peq vb a b) (peq vb a' b') := by
  intro v e
  rw [peq_eq_some] at *
  obtain ⟨u, w, h1, h2, rfl⟩ := e
  exact ⟨u, w, ha _ h1, hb _ h2, rfl⟩

theorem pite_mono {g g' a a' b b' : Option V} (hg : OLe g g') (ha : OLe a a') (hb : OLe b b') :
    OLe (pite vb g a b) (pite vb g' a' b') := by
  intro v e
  rw [pite_eq_some] at e ⊢
  rcases e with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨hg _ h1, ha _ h2⟩
  · refine .inr ⟨hg _ h1, ?_, hb _ h3⟩
    rw [hg _ h1]; rw [h1] at h2; exact h2

theorem pdistinct_mono {a a' : Option (List V)} (ha : OLe a a') :
    OLe (pdistinct vb a) (pdistinct vb a') := by
  intro v e
  cases a with
  | none => cases e
  | some vs => rw [ha vs rfl]; exact e

end

/-- The evaluation of the nodes is monotone in poison. -/
theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel Sem.FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · subst h; exact OLe.refl _
  · exact pnot_mono (h ρ)
  · exact pand_mono (h.1 ρ) (h.2 ρ)
  · exact por_mono (h.1 ρ) (h.2 ρ)
  · exact peq_mono (h.1 ρ) (h.2 ρ)
  · exact pite_mono (h.1 ρ) (h.2.1 ρ) (h.2.2 ρ)
  · exact pdistinct_mono (Sem.FLe.mapM h ρ)

end KanonBool

end
