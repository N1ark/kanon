import KanonCore.Model
import L4.Syntax

/-! The primitives of the rules: the literals of the bool module, and `ty`, the
`type_of` of the rules. -/

namespace L4

def ty (v : Term) : Ty := v.ty
def v_true : Term := .mk (.Bool true) .TBool
def v_false : Term := .mk (.Bool false) .TBool

end L4
