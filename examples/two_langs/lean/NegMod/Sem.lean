import Generated.NegMod.Node
import NumMod.Sem

/-!
# The meaning of the negation

The neg module evaluates its node with the integers of the num module: the
negation of an integer, and poison otherwise.
-/

noncomputable section

namespace NegMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- The neg module needs nothing more of the values of a language than the num
module does. -/
class Values (D : Kanon.Dom)

/-- The evaluation of a node, given the values of its children in every
environment. -/
def Node.eval {D : Kanon.Dom} [NumMod.Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Neg a => ((a ρ).bind NumMod.Values.vnum.proj).map fun z => NumMod.Values.vnum.inj (-z)

theorem Node.eval_mono {D : Kanon.Dom} [NumMod.Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel Sem.FLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n; cases n'; simp only [Node.Rel] at h
  rcases (h ρ).cases with h | h <;> simp [Node.eval, h]

end NegMod
