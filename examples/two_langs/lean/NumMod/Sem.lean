import NumMod.Node
import KanonBool.Sem

/-!
# The meaning of the nodes of the num module

The num module needs the integers among the values of a language
(`NumMod.Values`), and evaluates its nodes, given the values of their children:
`+`, `lt` and `max` are poison when an operand is, or is not an integer.
-/

noncomputable section

namespace NumMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- What the num module needs of the values of a language: its integers. -/
class Values (D : Kanon.Dom) where
  vnum : Embed Int D.Val

section
variable {V : Type} (vi : Embed Int V)

/-- An operation on two integers; poison otherwise. -/
def op2 {R : Type} (f : Int → Int → R) (a b : Option V) : Option R :=
  a.bind fun x => b.bind fun y => (vi.proj x).bind fun m => (vi.proj y).map fun n => f m n

@[kanon_val] theorem op2_eq_some {R : Type} {f : Int → Int → R} {a b : Option V} {r : R} :
    op2 vi f a b = some r ↔ ∃ m n, a = some (vi.inj m) ∧ b = some (vi.inj n) ∧ r = f m n := by
  constructor
  · intro h
    simp only [op2, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Embed.proj_eq_some_iff] at h
    obtain ⟨_, rfl, _, rfl, m, rfl, n, rfl, rfl⟩ := h
    exact ⟨m, n, rfl, rfl, rfl⟩
  · rintro ⟨m, n, rfl, rfl, rfl⟩
    simp [op2]

theorem op2_mono {R : Type} {f : Int → Int → R} {a a' b b' : Option V} (ha : OLe a a')
    (hb : OLe b b') : OLe (op2 vi f a b) (op2 vi f a' b') := by
  intro r e
  rw [op2_eq_some] at e ⊢
  obtain ⟨m, n, h1, h2, rfl⟩ := e
  exact ⟨m, n, ha _ h1, hb _ h2, rfl⟩
end

/-- The evaluation of a node, given the values of its children. -/
def Node.eval {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (Option D.Val) → Option D.Val
  | .Num z => some (Values.vnum.inj z)
  | .Add a b => op2 Values.vnum (fun m n => Values.vnum.inj (m + n)) a b
  | .Lt a b => op2 Values.vnum (fun m n => KanonBool.Values.vbool.inj (decide (m < n))) a b
  | .Max a b => op2 Values.vnum (fun m n => Values.vnum.inj (max m n)) a b

theorem Node.eval_mono {D : Kanon.Dom} [KanonBool.Values D] [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (Option D.Val)} (h : n.Rel OLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · subst h; exact OLe.refl _
  · exact op2_mono _ h.1 h.2
  · exact op2_mono _ h.1 h.2
  · exact op2_mono _ h.1 h.2

/-- The values of the sorts of the module: integers. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TNum, v => ∃ z, v = Values.vnum.inj z

end NumMod
