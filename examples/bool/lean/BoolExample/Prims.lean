import KanonCore
import BoolExample.Syntax

/-!
# The primitives of the rules

The Lean counterparts of the primitives that the bool module declares with
`prim` (the oracles, `tag_le` and `sort_by_tag`, are parameters of the model).
Hash-consed terms are modelled as trees, so that the physical equality of
hash-consed terms is structural equality.
-/

namespace BoolExample

open Classical

noncomputable def equal (a b : Term) : Bool := decide (a = b)
def ty (v : Term) : Ty := v.ty
def kind (v : Term) : Kind := v.kind
def v_true : Term := .mk (.Bool true) .TBool
def v_false : Term := .mk (.Bool false) .TBool

end BoolExample
