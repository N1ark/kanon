-- Option C feasibility: per-module node functors, a nested-inductive term, and
-- an evaluation that delegates to the modules (well-founded, so laws are `rw`, not `rfl`).
-- Check with `lake env lean OptionC.lean`.
import Exp.Val
open Exp
inductive Ty | TBool | TInt deriving DecidableEq
inductive Val | bool (b : Bool) | int (z : Int)
def Val.toBool : Val → Option Bool | .bool b => some b | _ => none
def Val.toInt : Val → Option Int | .int z => some z | _ => none
-- per-module node functors, owned by the modules (generic in the term type T)
inductive BK (T : Type) | lit (b : Bool) | not (a : T) | ite (g a b : T)
inductive IK (T : Type) | lit (z : Int) | add (a b : T)
-- per-module semantics of ONE node: the operands are evaluated by `r`, which
-- may only be called on the operands of the node (`sizeOf` bound), for termination
def BK.ev {T V : Type} [SizeOf T] (vb : Bool → V) (db : V → Option Bool) :
    (k : BK T) → ((x : T) → sizeOf x < sizeOf k → Option V) → Option V
  | .lit b, _ => some (vb b)
  | .not a, r => pnot vb db (r a (by simp <;> omega))
  | .ite g a b, r => pite db (r g (by simp <;> omega)) (r a (by simp <;> omega)) (r b (by simp <;> omega))
def IK.ev {T V : Type} [SizeOf T] (vi : Int → V) (di : V → Option Int) :
    (k : IK T) → ((x : T) → sizeOf x < sizeOf k → Option V) → Option V
  | .lit z, _ => some (vi z)
  | .add a b, r => padd vi di (r a (by simp <;> omega)) (r b (by simp <;> omega))
-- the language: a sum of the module functors (nested inductive)
inductive Term | var (x : Nat) (t : Ty) | b (k : BK Term) (t : Ty) | i (k : IK Term) (t : Ty)
-- evaluation, delegating to the modules
def ev (ρ : Nat → Val) : Term → Option Val
  | .var x _ => some (ρ x)
  | .b k _ => BK.ev .bool Val.toBool k (fun x _ => ev ρ x)
  | .i k _ => IK.ev .int Val.toInt k (fun x _ => ev ρ x)
-- the law that the generic proofs of B need, for this language:
theorem ev_not (ρ) (a : Term) (t) : ev ρ (.b (.not a) t) = pnot .bool Val.toBool (ev ρ a) := by
  rw [ev]; rfl
-- a third module added by another language reuses BK/IK and their `ev`
-- unchanged; only `Term` and `ev` (one line per module) are per-language.
