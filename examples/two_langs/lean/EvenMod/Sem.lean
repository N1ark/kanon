import EvenMod.Node
import NumMod.Sem

/-!
# The meaning of the nodes of the even module

Even integers are integers of the num module. The invariant of the sort
`TEven` (`even_inv`, part of the typing of its literals) is that its literals
are even.
-/

noncomputable section

namespace EvenMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- The even module needs nothing more of the values of a language than the
num module does. -/
class Values (D : Kanon.Dom)

/-- The invariant of the sort `TEven`: its literals are even. -/
@[kanon_wt] def even_inv {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sNum : NumMod.Srt → Ty)
    (sEven : Srt → Ty) (ty : T → Ty) : Node T → Ty → Prop
  | .Ev z, _ => z % 2 = 0
  | _, _ => True

/-- The evaluation of a node, given the values of its children in every
environment. -/
def Node.eval {D : Kanon.Dom} [NumMod.Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Ev z => some (NumMod.Values.vnum.inj z)
  | .Rem2 a => ((a ρ).bind NumMod.Values.vnum.proj).map fun z => NumMod.Values.vnum.inj (z % 2)

theorem Node.eval_mono {D : Kanon.Dom} [NumMod.Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel Sem.FLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  · subst h; exact OLe.refl _
  · rcases (h ρ).cases with h | h <;> simp [Node.eval, h]

/-- The values of the sort `TEven`: integers. -/
def Srt.val {D : Kanon.Dom} [NumMod.Values D] : Srt → D.Val → Prop
  | .TEven, v => ∃ z, v = NumMod.Values.vnum.inj z

end EvenMod
