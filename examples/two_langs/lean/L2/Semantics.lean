import KanonCore.Generic
import NegMod.Sem
import L2.Ops
import L2.Typing

/-!
# The semantics of terms, and refinement

The values are booleans and integers. The nodes of the bool module are
evaluated by the operations of `KanonBool.Val`, those of the num module by
those of `NumMod` (which it proves its rules with, once for both languages),
and the negation of the neg module by `NegMod.negV`.
-/

noncomputable section

namespace L2

open Classical Kanon KanonBool

mutual
/-- Syntactic well-typedness. -/
def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.Bool _) t => t = .TBool
  | .mk (.Num _) t => t = .TNum
  | .mk (.Op1 op a) t => op.WT a.ty t ∧ a.WT
  | .mk (.Op2 op a b) t => op.WT a.ty b.ty t ∧ a.WT ∧ b.WT
  | .mk (.Op3 op a b c) t => op.WT a.ty b.ty c.ty t ∧ a.WT ∧ b.WT ∧ c.WT
  | .mk (.OpN op l) t => ∃ e, op.WT e t ∧ Term.WTList e l

/-- All the terms are well-typed, of the type `e`. -/
def Term.WTList (e : Ty) : List Term → Prop
  | [] => True
  | x :: xs => x.ty = e ∧ x.WT ∧ Term.WTList e xs
end

/-- The typing of a list of terms, for the typing of `Distinct` in the
interface of the bool module (`kanon_law`). -/
@[kanon_law] theorem WTList_iff {e : Ty} :
    ∀ {l : List Term}, Term.WTList e l ↔ ∀ t ∈ l, t.ty = e ∧ t.WT
  | [] => by simp [Term.WTList]
  | t :: ts => by simp [Term.WTList, WTList_iff (l := ts), and_assoc]

/-- The values: booleans and integers. -/
inductive Val where
  | bool (b : Bool)
  | int (z : Int)
  deriving DecidableEq

/-- The type of a value. -/
def Val.ty : Val → Ty
  | .bool _ => .TBool
  | .int _ => .TNum

/-- The integer of a value, if it is one. -/
def Val.toInt : Val → Option Int
  | .int z => some z
  | _ => none

/-- The values of the variables; `none` for a poisoned variable. -/
abbrev Env := String → Option Val

def evOp1 : Op1 → Option Val → Option Val
  | .Not, a => pnot .bool a
  | .Neg, a => NegMod.negV .int Val.toInt a

def evOp2 : Op2 → Option Val → Option Val → Option Val
  | .And, a, b => pand .bool a b
  | .Or, a, b => por .bool a b
  | .Eq, a, b => peq .bool a b
  | .Add, a, b => NumMod.addV .int Val.toInt a b
  | .Lt, a, b => NumMod.ltV Val.toInt .bool a b
  | .Max, a, b => NumMod.maxV .int Val.toInt a b

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
  | .mk (.Num z) _ => some (.int z)
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

/-- The semantics of the language. -/
@[reducible] def sem : Sem where
  Term := Term
  Ty := Ty
  Val := Val
  Env := Env
  ty := Term.ty
  WT := Term.WT
  ev := ev

abbrev eval : Env → Term → Option Val := sem.eval
abbrev Refines : Term → Term → Prop := sem.Refines
instance : Refinement Refines := Sem.refinement

/-- What the proofs assume of the oracles: what the bool module assumes of
`sort_by_tag`. -/
structure Oracle.Compat (orc : Oracle) : Prop where
  bool : KanonBool.Oracle.Compat orc.sort_by_tag

end L2

end
