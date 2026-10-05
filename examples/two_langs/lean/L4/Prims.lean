import KanonCore.Model
import L4.Syntax

/-! The primitives of the rules: the literals of the bool module, `ty`, the
`type_of` of the rules, and `fit`, the width of an integer. -/

namespace L4

def ty (v : Term) : Ty := v.ty
def v_true : Term := .mk (.Bool true) .TBool
def v_false : Term := .mk (.Bool false) .TBool
def fit (z : Int) : Int := z.natAbs.log2 + 1

end L4
