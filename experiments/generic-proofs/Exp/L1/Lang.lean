import Exp.Val
import KanonCore.Refinement
import KanonCore.Option

/-! Language 1 (B + I + variables), as Kanon generates it today: a closed
term type, its typing and semantics, the model of its rule functions, and the
statements of the arms. -/

set_option linter.unusedVariables false

noncomputable section

namespace Exp.L1

open Classical Kanon

inductive Ty | TBool | TInt
  deriving DecidableEq, Inhabited

inductive Val | bool (b : Bool) | int (z : Int)
  deriving DecidableEq, Inhabited

def Val.toBool : Val → Option Bool | .bool b => some b | _ => none
def Val.toInt : Val → Option Int | .int z => some z | _ => none
def Val.ty : Val → Ty | .bool _ => .TBool | .int _ => .TInt

mutual
inductive Kind where
  | Var : Nat → Kind
  | BLit : Bool → Kind
  | BNot : Term → Kind
  | BIte : Term → Term → Term → Kind
  | BEq : Term → Term → Kind
  | ILit : Int → Kind
  | Add : Term → Term → Kind
  | Lt : Term → Term → Kind
  | OfBool : Term → Kind
inductive Term where
  | mk (kind : Kind) (ty : Ty)
end

instance : Inhabited Term := ⟨.mk (.Var 0) .TBool⟩

def Term.ty : Term → Ty | .mk _ t => t

def Term.WT : Term → Prop
  | .mk (.Var _) _ => True
  | .mk (.BLit _) t => t = .TBool
  | .mk (.BNot a) t => a.ty = .TBool ∧ t = .TBool ∧ a.WT
  | .mk (.BIte g a b) t => g.ty = .TBool ∧ a.ty = t ∧ b.ty = t ∧ g.WT ∧ a.WT ∧ b.WT
  | .mk (.BEq a b) t => b.ty = a.ty ∧ t = .TBool ∧ a.WT ∧ b.WT
  | .mk (.ILit _) t => t = .TInt
  | .mk (.Add a b) t => a.ty = .TInt ∧ b.ty = .TInt ∧ t = .TInt ∧ a.WT ∧ b.WT
  | .mk (.Lt a b) t => a.ty = .TInt ∧ b.ty = .TInt ∧ t = .TBool ∧ a.WT ∧ b.WT
  | .mk (.OfBool a) t => a.ty = .TBool ∧ t = .TInt ∧ a.WT

abbrev Env := Nat → Val

noncomputable def ev (ρ : Env) : Term → Option Val
  | .mk (.Var x) t => if (ρ x).ty = t then some (ρ x) else none
  | .mk (.BLit b) _ => some (.bool b)
  | .mk (.BNot a) _ => pnot .bool Val.toBool (ev ρ a)
  | .mk (.BIte g a b) _ => pite Val.toBool (ev ρ g) (ev ρ a) (ev ρ b)
  | .mk (.BEq a b) _ => peq .bool (ev ρ a) (ev ρ b)
  | .mk (.ILit z) _ => some (.int z)
  | .mk (.Add a b) _ => padd .int Val.toInt (ev ρ a) (ev ρ b)
  | .mk (.Lt a b) _ => plt .bool Val.toInt (ev ρ a) (ev ρ b)
  | .mk (.OfBool a) _ => pofbool .int Val.toBool (ev ρ a)

@[reducible] def sem : Sem where
  Term := Term
  Ty := Ty
  Val := Val
  Env := Env
  ty := Term.ty
  WT := Term.WT
  ev := ev

abbrev Refines := sem.Refines
instance : Refinement Refines := Sem.refinement

/-! ## The model: rule functions, with the closed matches Kanon generates -/

structure Ops where
  not_ : Term → Term
  ite : Term → Term → Term → Term
  eq : Term → Term → Term
  add : Term → Term → Term
  lt : Term → Term → Term
  of_bool : Term → Term
  tag_le : Term → Term → Bool

def B.not_.spec (a : Term) : Term := .mk (.BNot a) .TBool
def B.ite.spec (g a b : Term) : Term := .mk (.BIte g a b) a.ty
def B.eq.spec (a b : Term) : Term := .mk (.BEq a b) .TBool
def I.add.spec (a b : Term) : Term := .mk (.Add a b) .TInt
def I.lt.spec (a b : Term) : Term := .mk (.Lt a b) .TBool
def I.of_bool.spec (a : Term) : Term := .mk (.OfBool a) .TInt

structure Ops.Sound (O : Ops) : Prop where
  not_ : ∀ a, Refines (B.not_.spec a) (O.not_ a)
  ite : ∀ g a b, Refines (B.ite.spec g a b) (O.ite g a b)
  eq : ∀ a b, Refines (B.eq.spec a b) (O.eq a b)
  add : ∀ a b, Refines (I.add.spec a b) (O.add a b)
  lt : ∀ a b, Refines (I.lt.spec a b) (O.lt a b)
  of_bool : ∀ a, Refines (I.of_bool.spec a) (O.of_bool a)

/-- The extensible helper `sure_neq`: the case of `B`, then that of `I`. -/
def B.sure_neq.c_bool (a b : Term) : Option Bool :=
  match a, b with
  | .mk (.BLit x) _, .mk (.BLit y) _ => some (!decide (x = y))
  | _, _ => none
def I.sure_neq.c_int (a b : Term) : Option Bool :=
  match a, b with
  | .mk (.ILit x) _, .mk (.ILit y) _ => some (!decide (x = y))
  | _, _ => none
def B.sure_neq (a b : Term) : Bool :=
  (firstSome [B.sure_neq.c_bool a b, I.sure_neq.c_int a b]).getD false

def B.not_.r_lit (O : Ops) (v : Term) : Option Term :=
  match v with | .mk (.BLit b) _ => some (.mk (.BLit (!b)) .TBool) | _ => none
def B.not_.r_nn (O : Ops) (v : Term) : Option Term :=
  match v with | .mk (.BNot a) _ => some a | _ => none
def B.not_.r_lt (O : Ops) (v : Term) : Option Term :=
  match v with | .mk (.Lt a b) _ => some (O.lt b (O.add a (.mk (.ILit 1) .TInt))) | _ => none
def B.not_.r_default (O : Ops) (v : Term) : Option Term := some (.mk (.BNot v) .TBool)
def B.not_.step (O : Ops) (v : Term) : Term :=
  (firstSome [B.not_.r_lit O v, B.not_.r_nn O v, B.not_.r_lt O v, B.not_.r_default O v]).getD
    (B.not_.spec v)

def B.ite.r_true (O : Ops) (g a b : Term) : Option Term :=
  match g with | .mk (.BLit true) _ => some a | _ => none
def B.ite.r_same (O : Ops) (g a b : Term) : Option Term :=
  if decide (a = b) then some a else none
def B.ite.r_bool (O : Ops) (g a b : Term) : Option Term :=
  match a, b with | .mk (.BLit true) _, .mk (.BLit false) _ => some g | _, _ => none
def B.ite.r_default (O : Ops) (g a b : Term) : Option Term := some (B.ite.spec g a b)
def B.ite.step (O : Ops) (g a b : Term) : Term :=
  (firstSome [B.ite.r_true O g a b, B.ite.r_same O g a b, B.ite.r_bool O g a b,
    B.ite.r_default O g a b]).getD (B.ite.spec g a b)

def B.eq.r_ints (O : Ops) (a b : Term) : Option Term :=
  match a, b with
  | .mk (.ILit x) _, .mk (.ILit y) _ => some (.mk (.BLit (decide (x = y))) .TBool)
  | _, _ => none
def B.eq.r_same (O : Ops) (a b : Term) : Option Term :=
  if decide (a = b) then some (.mk (.BLit true) .TBool) else none
def B.eq.r_neq (O : Ops) (a b : Term) : Option Term :=
  if B.sure_neq a b then some (.mk (.BLit false) .TBool) else none
def B.eq.r_lits (O : Ops) (a b : Term) : Option Term :=
  match a, b with
  | .mk (.BLit x) _, .mk (.BLit y) _ => some (.mk (.BLit (decide (x = y))) .TBool)
  | _, _ => none
def B.eq.r_default (O : Ops) (a b : Term) : Option Term :=
  some (.mk (if O.tag_le a b then .BEq a b else .BEq b a) .TBool)
def B.eq.step (O : Ops) (a b : Term) : Term :=
  (firstSome [B.eq.r_ints O a b, B.eq.r_same O a b, B.eq.r_neq O a b, B.eq.r_lits O a b,
    B.eq.r_default O a b]).getD (B.eq.spec a b)

def I.add.r_lits (O : Ops) (a b : Term) : Option Term :=
  match a, b with
  | .mk (.ILit x) _, .mk (.ILit y) _ => some (.mk (.ILit (x + y)) .TInt)
  | _, _ => none
def I.add.r_zero (O : Ops) (a b : Term) : Option Term :=
  match a with | .mk (.ILit 0) _ => some b | _ => none
def I.add.r_ite (O : Ops) (a b : Term) : Option Term :=
  match a with | .mk (.BIte g x y) _ => some (O.ite g (O.add x b) (O.add y b)) | _ => none
def I.add.r_default (O : Ops) (a b : Term) : Option Term :=
  some (.mk (if O.tag_le a b then .Add a b else .Add b a) .TInt)
def I.add.step (O : Ops) (a b : Term) : Term :=
  (firstSome [I.add.r_lits O a b, I.add.r_zero O a b, I.add.r_ite O a b,
    I.add.r_default O a b]).getD (I.add.spec a b)

def I.lt.r_lits (O : Ops) (a b : Term) : Option Term :=
  match a, b with
  | .mk (.ILit x) _, .mk (.ILit y) _ => some (.mk (.BLit (decide (x < y))) .TBool)
  | _, _ => none
def I.lt.r_same (O : Ops) (a b : Term) : Option Term :=
  if decide (a = b) then some (.mk (.BLit false) .TBool) else none
def I.lt.r_ofbool (O : Ops) (a b : Term) : Option Term :=
  match a, b with
  | .mk (.OfBool _) _, .mk (.ILit z) _ => if decide (1 < z) then some (.mk (.BLit true) .TBool) else none
  | _, _ => none
def I.lt.r_default (O : Ops) (a b : Term) : Option Term := some (I.lt.spec a b)
def I.lt.step (O : Ops) (a b : Term) : Term :=
  (firstSome [I.lt.r_lits O a b, I.lt.r_same O a b, I.lt.r_ofbool O a b,
    I.lt.r_default O a b]).getD (I.lt.spec a b)

def I.of_bool.r_true (O : Ops) (a : Term) : Option Term :=
  match a with | .mk (.BLit true) _ => some (.mk (.ILit 1) .TInt) | _ => none
def I.of_bool.r_false (O : Ops) (a : Term) : Option Term :=
  match a with | .mk (.BLit false) _ => some (.mk (.ILit 0) .TInt) | _ => none
def I.of_bool.r_default (O : Ops) (a : Term) : Option Term := some (I.of_bool.spec a)
def I.of_bool.step (O : Ops) (a : Term) : Term :=
  (firstSome [I.of_bool.r_true O a, I.of_bool.r_false O a, I.of_bool.r_default O a]).getD
    (I.of_bool.spec a)

/-! ## The statements of the arms (pattern-instantiated, as Kanon generates them) -/

def B.not_.lit.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (b : Bool) (t : Ty),
  Refines (B.not_.spec (.mk (.BLit b) t)) (.mk (.BLit (!b)) .TBool)
def B.not_.nn.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a : Term) (t : Ty),
  Refines (B.not_.spec (.mk (.BNot a) t)) a
def B.not_.lt.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term) (t : Ty),
  Refines (B.not_.spec (.mk (.Lt a b) t)) (O.lt b (O.add a (.mk (.ILit 1) .TInt)))
def B.not_.default.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (v : Term),
  Refines (B.not_.spec v) (.mk (.BNot v) .TBool)
def B.ite.true_.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term) (t : Ty),
  Refines (B.ite.spec (.mk (.BLit true) t) a b) a
def B.ite.same.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (g a b : Term), decide (a = b) = true →
  Refines (B.ite.spec g a b) a
def B.ite.bool.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (g : Term) (t1 t2 : Ty),
  Refines (B.ite.spec g (.mk (.BLit true) t1) (.mk (.BLit false) t2)) g
def B.ite.default.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (g a b : Term),
  Refines (B.ite.spec g a b) (B.ite.spec g a b)
def B.eq.ints.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (x : Int) (t1 : Ty) (y : Int) (t2 : Ty),
  Refines (B.eq.spec (.mk (.ILit x) t1) (.mk (.ILit y) t2)) (.mk (.BLit (decide (x = y))) .TBool)
def B.eq.same.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term), decide (a = b) = true →
  Refines (B.eq.spec a b) (.mk (.BLit true) .TBool)
def B.eq.neq.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term), B.sure_neq a b = true →
  Refines (B.eq.spec a b) (.mk (.BLit false) .TBool)
def B.eq.lits.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (x : Bool) (t1 : Ty) (y : Bool) (t2 : Ty),
  Refines (B.eq.spec (.mk (.BLit x) t1) (.mk (.BLit y) t2)) (.mk (.BLit (decide (x = y))) .TBool)
def B.eq.default.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term),
  Refines (B.eq.spec a b) (.mk (if O.tag_le a b then .BEq a b else .BEq b a) .TBool)
def I.add.lits.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (x : Int) (t1 : Ty) (y : Int) (t2 : Ty),
  Refines (I.add.spec (.mk (.ILit x) t1) (.mk (.ILit y) t2)) (.mk (.ILit (x + y)) .TInt)
def I.add.zero.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (t1 : Ty) (b : Term),
  Refines (I.add.spec (.mk (.ILit 0) t1) b) b
def I.add.ite.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (g x y : Term) (t : Ty) (b : Term),
  Refines (I.add.spec (.mk (.BIte g x y) t) b) (O.ite g (O.add x b) (O.add y b))
def I.add.default.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term),
  Refines (I.add.spec a b) (.mk (if O.tag_le a b then .Add a b else .Add b a) .TInt)
def I.lt.lits.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (x : Int) (t1 : Ty) (y : Int) (t2 : Ty),
  Refines (I.lt.spec (.mk (.ILit x) t1) (.mk (.ILit y) t2)) (.mk (.BLit (decide (x < y))) .TBool)
def I.lt.same.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term), decide (a = b) = true →
  Refines (I.lt.spec a b) (.mk (.BLit false) .TBool)
def I.lt.ofbool.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (c : Term) (t : Ty) (z : Int) (t2 : Ty),
  decide (1 < z) = true →
  Refines (I.lt.spec (.mk (.OfBool c) t) (.mk (.ILit z) t2)) (.mk (.BLit true) .TBool)
def I.lt.default.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a b : Term),
  Refines (I.lt.spec a b) (I.lt.spec a b)
def I.of_bool.true_.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (t : Ty),
  Refines (I.of_bool.spec (.mk (.BLit true) t)) (.mk (.ILit 1) .TInt)
def I.of_bool.false_.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (t : Ty),
  Refines (I.of_bool.spec (.mk (.BLit false) t)) (.mk (.ILit 0) .TInt)
def I.of_bool.default.Stmt : Prop := ∀ (O : Ops), O.Sound → ∀ (a : Term),
  Refines (I.of_bool.spec a) (I.of_bool.spec a)

end Exp.L1

end
