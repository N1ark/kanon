import ArraysExample.Vec.Node
import KanonCore.Embed
import KanonCore.Array
import KanonCore.ProofAttr

/-!
# The meaning of the nodes of the vec module

The module needs integers and arrays of integers among the values of a
language (`Values`). Reading or writing out of the bounds of an array is
poison.
-/

noncomputable section

namespace ArraysExample.Vec

open Classical Kanon
open Kanon.Sem (OLe)

/-- What the module needs of the values of a language: integers and arrays of
integers. -/
class Values (D : Kanon.Dom) where
  vint : Embed Int D.Val
  vvec : Embed (Array Int) D.Val

/-- Whether an index is in the bounds of an array. -/
def inBounds (a : Array Int) (i : Int) : Prop := 0 ≤ i ∧ i < arrayLength a

section
variable {D : Kanon.Dom} [Values D]

/-- The length of an array. -/
def lenV (a : Option D.Val) : Option D.Val :=
  (a.bind Values.vvec.proj).map fun a => Values.vint.inj (arrayLength a)

/-- The element of an array at an index in its bounds; poison otherwise. -/
def getV (a i : Option D.Val) : Option D.Val :=
  (a.bind Values.vvec.proj).bind fun a => (i.bind Values.vint.proj).bind fun i =>
    if inBounds a i then some (Values.vint.inj (arrayGet a i)) else none

/-- An array with the element at an index in its bounds replaced; poison
otherwise. -/
def setV (a i x : Option D.Val) : Option D.Val :=
  (a.bind Values.vvec.proj).bind fun a => (i.bind Values.vint.proj).bind fun i =>
    (x.bind Values.vint.proj).bind fun x =>
      if inBounds a i then some (Values.vvec.inj (arraySet a i x)) else none
end

/-! The operations are unfolded once the values of their operands are known. -/
attribute [kanon_val] lenV getV setV inBounds

/-- The evaluation of a node, given the values of its children in every
environment. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Int z => some (Values.vint.inj z)
  | .Vec a => some (Values.vvec.inj a)
  | .Len a => lenV (a ρ)
  | .Get a i => getV (a ρ) (i ρ)
  | .Set a i x => setV (a ρ) (i ρ) (x ρ)

theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel Sem.FLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · subst h; exact OLe.refl _
  · subst h; exact OLe.refl _
  · rcases (h ρ).cases with h | h <;> simp [h, lenV]
  · rcases (h.1 ρ).cases with h1 | h1 <;> rcases (h.2 ρ).cases with h2 | h2 <;> simp [h1, h2, getV]
  · rcases (h.1 ρ).cases with h1 | h1 <;> rcases (h.2.1 ρ).cases with h2 | h2 <;>
      rcases (h.2.2 ρ).cases with h3 | h3 <;> simp [h1, h2, h3, setV]

/-- The values of the sorts of the module: integers and arrays. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TInt, v => ∃ z, v = Values.vint.inj z
  | .TVec, v => ∃ a, v = Values.vvec.inj a

end ArraysExample.Vec
