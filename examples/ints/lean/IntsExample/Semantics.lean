import KanonCore.Sem
import KanonCore.BoolMod.Val
import IntsExample.Model
import IntsExample.Typing

/-!
# The semantics of terms, and refinement

`eval ρ t` is the value of the term `t` under the environment `ρ`, a boolean or
an integer, or `none` for *poison*:

- ill-typed terms (see `Term.WT`) are poison, and so are the variables that
  `ρ` does not give a value of their type;
- the nodes of the bool module are evaluated by the operations of Kanon's
  library (`Kanon.BoolMod.Val`): `&&` and `||` are "parallel" (a `false`,
  resp. `true`, operand wins over a poisoned one), `ite` only evaluates the
  branch it selects;
- `+` and `lt` are poison when an operand is.

A smart constructor is sound when its result *refines* the raw node it
simplifies (`Refines`, Kanon's `Sem.Refines`): whenever the raw node is
well-typed, the result is well-typed, of the same type, and whenever the raw
node evaluates to a value, the result evaluates to the same value.
-/

noncomputable section

namespace IntsExample

open Classical Kanon BoolMod

/-! ## Well-typed terms -/

/-! The typing of the operators, `Op1.WT`, `Op2.WT`, `Op3.WT` and `OpN.WT`
(over the type of all the operands of an n-ary operator), is generated from
the declarations of the nodes in `Typing.lean`. -/

mutual
/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.Bool _) t => t = .TBool
  | .mk (.Int _) t => t = .TInt
  | .mk (.Op1 op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Op2 op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT
  | .mk (.Op3 op a b c) t => op.WT a.ty b.ty c.ty t ∧ a.WT ∧ b.WT ∧ c.WT
  | .mk (.OpN op l) t => ∃ e, op.WT e t ∧ Term.WTList e l

/-- All the terms are well-typed, of the type `e`. -/
def Term.WTList (e : Ty) : List Term → Prop
  | [] => True
  | x :: xs => x.ty = e ∧ x.WT ∧ Term.WTList e xs
end

/-! ## Values and evaluation -/

/-- The values: booleans and integers. -/
inductive Val where
  | bool (b : Bool)
  | int (z : Int)
  deriving DecidableEq

/-- The type of a value. -/
def Val.ty : Val → Ty
  | .bool _ => .TBool
  | .int _ => .TInt

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

/-- The sum of two integers; poison otherwise. -/
def addV : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => some (.int (x + y))
  | _, _ => none

/-- The order of two integers; poison otherwise. -/
def ltV : Option Val → Option Val → Option Val
  | some (.int x), some (.int y) => some (.bool (decide (x < y)))
  | _, _ => none

def evOp1 : Op1 → Option Val → Option Val
  | .Not, a => pnot .bool a

def evOp2 : Op2 → Option Val → Option Val → Option Val
  | .And, a, b => pand .bool a b
  | .Or, a, b => por .bool a b
  | .Eq, a, b => peq .bool a b
  | .Plus, a, b => addV a b
  | .Lt, a, b => ltV a b

def evOp3 : Op3 → Option Val → Option Val → Option Val → Option Val
  | .Ite, g, a, b => pite .bool g a b

def evOpN : OpN → Option (List Val) → Option Val
  | .Distinct, vs => pdistinct .bool vs

mutual
/-- Evaluation, assuming well-typedness. A variable is poison unless `ρ`
gives it a value of its type. -/
def ev (ρ : Env) : Term → Option Val
  | .mk (.Var x) t => match ρ x with
    | some v => if v.ty = t then some v else none
    | none => none
  | .mk (.Bool b) _ => some (.bool b)
  | .mk (.Int z) _ => some (.int z)
  | .mk (.Op1 op a) _ => evOp1 op (ev ρ a)
  | .mk (.Op2 op a b) _ => evOp2 op (ev ρ a) (ev ρ b)
  | .mk (.Op3 op a b c) _ => evOp3 op (ev ρ a) (ev ρ b) (ev ρ c)
  | .mk (.OpN op l) _ => evOpN op (evList ρ l)

/-- The values of a list of terms, if none is poison. -/
def evList (ρ : Env) : List Term → Option (List Val)
  | [] => some []
  | t :: ts =>
      match ev ρ t, evList ρ ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

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

/-! ## Assumptions on the oracles -/

/-- What the proofs assume of the oracles: that sorting by tags permutes a
list. The hash-consing order `tag_le` is arbitrary. -/
structure Oracle.Compat (orc : Oracle) : Prop where
  sort_by_tag : ∀ l, (orc.sort_by_tag l).Perm l

end IntsExample

end
