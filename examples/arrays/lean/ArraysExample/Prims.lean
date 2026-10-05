import KanonCore.Model
import ArraysExample.Syntax

/-!
# The primitives of the rules

The Lean counterparts of the primitives that the rules declare with `prim`
(`Signatures.lean` checks their types); `ty` is what the rules write `type_of`.
Terms are trees, so that the equality of hash-consed terms, which the model compares with
`decide (a = b)`, is structural equality.
-/

namespace ArraysExample

def ty (v : Term) : Ty := v.ty

end ArraysExample
