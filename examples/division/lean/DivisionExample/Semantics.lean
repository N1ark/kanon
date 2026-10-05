import KanonCore.Generic
import DivMod.Sem
import DivisionExample.Ops
import DivisionExample.Typing

/-!
# The semantics of terms, and refinement

`eval ρ t` is the value of the term `t` under the environment `ρ`, an integer,
or `none` for *poison*:

- ill-typed terms (see `Term.WT`) are poison, and so are the variables that
  `ρ` does not give a value of their type;
- `+`, `/` and `Sq1` are evaluated by the operations of the int module
  (`DivMod.addV`, ...): poison when an operand is; the quotient by zero is
  zero, as in Lean, which is why a division needs a non-zero divisor (the
  subsort `TNonzero`, whose Lean predicate is `Nonzero`).

The int module is proved once, over its interface (`DivMod`): `Lang.lean` gives
what it needs of this semantics.

A smart constructor is sound when its result *refines* the raw node it
simplifies (`Refines`, Kanon's `Sem.Refines`): whenever the raw node is
well-typed, the result is well-typed, of the same type, and whenever the raw
node evaluates to a value, the result evaluates to the same value.
-/

noncomputable section

namespace DivisionExample

open Classical Kanon

/-! ## Well-typed terms -/

/-! The typing of the operators, `Op1.WT` and `Op2.WT`, is generated from the
declarations of the nodes in `Typing.lean`. -/

/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.Int _) t => t = .TInt
  | .mk (.Op1 op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Op2 op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT

/-! ## Values and evaluation -/

/-- The values: integers. -/
inductive Val where
  | int (z : Int)
  deriving DecidableEq

/-- The type of a value. -/
def Val.ty : Val → Ty
  | .int _ => .TInt

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

/-- The integer of a value. -/
def Val.toInt : Val → Option Int
  | .int z => some z

def evOp1 : Op1 → Option Val → Option Val
  | .Sq1, a => DivMod.sq1V .int Val.toInt a

def evOp2 : Op2 → Option Val → Option Val → Option Val
  | .Plus, a, b => DivMod.addV .int Val.toInt a b
  | .Div, a, b => DivMod.divV .int Val.toInt a b

/-- Evaluation, assuming well-typedness. A variable is poison unless `ρ`
gives it a value of its type. -/
def ev (ρ : Env) : Term → Option Val
  | .mk (.Var x) t => match ρ x with
    | some v => if v.ty = t then some v else none
    | none => none
  | .mk (.Int z) _ => some (.int z)
  | .mk (.Op1 op a) _ => evOp1 op (ev ρ a)
  | .mk (.Op2 op a b) _ => evOp2 op (ev ρ a) (ev ρ b)


/-! ## Refinement -/

/-- The semantics of the language. -/
@[reducible] def sem : Sem where
  Term := Term
  Ty := Ty
  Val := Val
  Env := Env
  ty := Term.ty
  WT := Term.WT
  ev := ev

/-- The value of a term; `none` for poison. -/
abbrev eval : Env → Term → Option Val := sem.eval

/-- `r` refines `spec`: it has the same type, and the same value whenever
`spec` is not poison. -/
abbrev Refines : Term → Term → Prop := sem.Refines

instance : Refinement Refines := Sem.refinement

/-- A term is not zero: whenever it has an integer value, it is not zero. This
is the meaning of the subsort `TNonzero` (`[@lean "Nonzero"]`), which the
statements of the rules assume of the divisor of a division, and the rules that
return a `Sq1` must prove of their results. -/
def Nonzero (t : Term) : Prop := ∀ ρ z, eval ρ t = some (.int z) → z ≠ 0

/-! ## Assumptions on the oracles -/

/-- What the proofs assume of the oracles: nothing, the hash-consing order
`tag_le` is arbitrary. -/
structure Oracle.Compat (orc : Oracle) : Prop

end DivisionExample

end
