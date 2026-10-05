import KanonCore.Sem
import KanonCore.Array
import ArraysExample.Ops
import ArraysExample.Typing

/-!
# The semantics of terms, and refinement

`eval ρ t` is the value of the term `t`, an integer or an array of integers, or
`none` for *poison*: ill-typed terms (see `Term.WT`) are poison, and so are the
nodes that read or write an array out of its bounds, or that an operand of
which is. The language has no variables (`Env` is `Unit`).

Its module, `vec`, is proved for this language only (it does not declare a
`[@@@lean_module]`): the statements of its arms are over the terms of the
language, as the rules of a module were before the modules proved once.
-/

noncomputable section

namespace ArraysExample

open Classical Kanon

/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Int _) t => t = .TInt
  | .mk (.Vec _) t => t = .TVec
  | .mk (.Op1 op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Op2 op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT
  | .mk (.Op3 op a b c) t => op.WT a.ty b.ty c.ty t ∧ a.WT ∧ b.WT ∧ c.WT

/-- The values: integers and arrays of integers. -/
inductive Val where
  | int (z : Int)
  | vec (a : Array Int)
  deriving DecidableEq

/-- No variables. -/
abbrev Env := Unit

/-- Whether an index is in the bounds of an array. -/
def inBounds (a : Array Int) (i : Int) : Prop := 0 ≤ i ∧ i < arrayLength a

/-- The length of an array. -/
def lenV : Option Val → Option Val
  | some (.vec a) => some (.int (arrayLength a))
  | _ => none

/-- The element of an array at an index in its bounds; poison otherwise. -/
def getV : Option Val → Option Val → Option Val
  | some (.vec a), some (.int i) => if inBounds a i then some (.int (arrayGet a i)) else none
  | _, _ => none

/-- An array with the element at an index in its bounds replaced; poison
otherwise. -/
def setV : Option Val → Option Val → Option Val → Option Val
  | some (.vec a), some (.int i), some (.int x) =>
    if inBounds a i then some (.vec (arraySet a i x)) else none
  | _, _, _ => none

def evOp1 : Op1 → Option Val → Option Val
  | .Len, a => lenV a

def evOp2 : Op2 → Option Val → Option Val → Option Val
  | .Get, a, b => getV a b

def evOp3 : Op3 → Option Val → Option Val → Option Val → Option Val
  | .Set, a, b, c => setV a b c

/-- Evaluation, assuming well-typedness. -/
def ev (ρ : Env) : Term → Option Val
  | .mk (.Int z) _ => some (.int z)
  | .mk (.Vec a) _ => some (.vec a)
  | .mk (.Op1 op a) _ => evOp1 op (ev ρ a)
  | .mk (.Op2 op a b) _ => evOp2 op (ev ρ a) (ev ρ b)
  | .mk (.Op3 op a b c) _ => evOp3 op (ev ρ a) (ev ρ b) (ev ρ c)

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

/-- What the proofs assume of the oracles: nothing. -/
structure Oracle.Compat (orc : Oracle) : Prop

end ArraysExample

end
