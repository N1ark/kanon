import KanonCore.Model
import IntsExample.Syntax

/-!
# The primitives of the rules

The Lean counterparts of the primitives that the rules declare with `prim`
(`Signatures.lean` checks their types). The bool module declares `v_true` and
`v_false`; `ty` is what the rules write `type_of`. Terms are trees, so that
the equality of hash-consed terms, which the model compares with
`decide (a = b)`, is structural equality.
-/

namespace IntsExample

def ty (v : Term) : Ty := v.ty
def v_true : Term := .mk (.Bool true) .TBool
def v_false : Term := .mk (.Bool false) .TBool

end IntsExample
