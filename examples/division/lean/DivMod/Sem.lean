import DivMod.Node
import KanonCore.Embed
import KanonCore.ProofAttr

/-!
# The meaning of the nodes of the int module

The module needs the integers among the values of a language
(`DivMod.Values`), and evaluates its nodes, given the values of their
children: poison when an operand is, or is not an integer. The quotient by zero
is zero, as in Lean.
-/

noncomputable section

namespace DivMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- What the module needs of the values of a language: its integers. -/
class Values (D : Kanon.Dom) where
  vint : Embed Int D.Val

section
variable {V : Type} (vi : Embed Int V)

/-- An operation on one integer; poison otherwise. -/
def op1 (f : Int → Int) (a : Option V) : Option V :=
  a.bind fun x => (vi.proj x).map fun m => vi.inj (f m)

/-- An operation on two integers; poison otherwise. -/
def op2 (f : Int → Int → Int) (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (vi.proj x).bind fun m => (vi.proj y).map fun n => vi.inj (f m n)

@[kanon_val] theorem op1_eq_some {f : Int → Int} {a : Option V} {r : V} :
    op1 vi f a = some r ↔ ∃ m, a = some (vi.inj m) ∧ r = vi.inj (f m) := by
  constructor
  · intro h
    simp only [op1, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Embed.proj_eq_some_iff] at h
    obtain ⟨_, rfl, m, rfl, rfl⟩ := h
    exact ⟨m, rfl, rfl⟩
  · rintro ⟨m, rfl, rfl⟩
    simp [op1]

@[kanon_val] theorem op2_eq_some {f : Int → Int → Int} {a b : Option V} {r : V} :
    op2 vi f a b = some r ↔ ∃ m n, a = some (vi.inj m) ∧ b = some (vi.inj n) ∧ r = vi.inj (f m n) := by
  constructor
  · intro h
    simp only [op2, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Embed.proj_eq_some_iff] at h
    obtain ⟨_, rfl, _, rfl, m, rfl, n, rfl, rfl⟩ := h
    exact ⟨m, n, rfl, rfl, rfl⟩
  · rintro ⟨m, n, rfl, rfl, rfl⟩
    simp [op2]

theorem op1_mono {f : Int → Int} {a a' : Option V} (ha : OLe a a') :
    OLe (op1 vi f a) (op1 vi f a') := by
  intro r e
  rw [op1_eq_some] at e ⊢
  obtain ⟨m, h1, rfl⟩ := e
  exact ⟨m, ha _ h1, rfl⟩

theorem op2_mono {f : Int → Int → Int} {a a' b b' : Option V} (ha : OLe a a') (hb : OLe b b') :
    OLe (op2 vi f a b) (op2 vi f a' b') := by
  intro r e
  rw [op2_eq_some] at e ⊢
  obtain ⟨m, n, h1, h2, rfl⟩ := e
  exact ⟨m, n, ha _ h1, hb _ h2, rfl⟩
end

/-- The evaluation of a node, given the values of its children. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (Option D.Val) → Option D.Val
  | .Int z => some (Values.vint.inj z)
  | .Plus a b => op2 Values.vint (· + ·) a b
  | .Div a b => op2 Values.vint (· / ·) a b
  | .Sq1 a => op1 Values.vint (fun m => m * m + 1) a

theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (Option D.Val)} (h : n.Rel OLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · subst h; exact OLe.refl _
  · exact op2_mono _ h.1 h.2
  · exact op2_mono _ h.1 h.2
  · exact op1_mono _ h

/-- The values of the sorts of the module: integers. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TInt, v => ∃ z, v = Values.vint.inj z

end DivMod
