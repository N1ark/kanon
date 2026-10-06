import BoolExample.Node
import KanonCore.Embed

/-!
# The meaning of the variables

The module of the language (`../lang.knl`) declares its variables, `Var x`: a
variable is the value that the environment gives it, or poison.
-/

namespace BoolExample

open Kanon
open Kanon.Sem (OLe)

/-- What the variables need of a language: the values of the variables in an
environment. -/
class Values (D : Kanon.Dom) where
  lookup : D.Env → Int → Option D.Val

/-- The value of a variable. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (Option D.Val) → Option D.Val
  | .Var x => Values.lookup ρ x

theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (Option D.Val)} (h : n.Rel OLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n; cases n'; simp only [Node.Rel] at h; subst h; exact OLe.refl _

end BoolExample
