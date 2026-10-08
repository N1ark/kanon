import L2.Generated.Node
import KanonCore.Embed

/-!
# The meaning of the variables

A variable is the value that the environment gives it, if it is of the sort of
the variable, and poison otherwise.
-/

noncomputable section

namespace L2

open Classical Kanon
open Kanon.Sem (OLe)

/-- What the variables need of a language: the values of the variables in an
environment, and the values of each sort. -/
class Values (D : Kanon.Dom) where
  lookup : D.Env → String → Option D.Val
  Of : D.Val → D.Ty → Prop

/-- The value of a variable, at its sort. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Var x => (Values.lookup ρ x).bind fun v => if Values.Of v t then some v else none

theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel Sem.FLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n; cases n'; simp only [Node.Rel] at h; subst h; exact OLe.refl _

end L2
