import Exp.L2.Step
import Exp.Generic.XMod

/-! Option B: language 2 instantiates the interfaces of its modules, and its
arms are the generic theorems. -/

set_option linter.unusedVariables false

noncomputable section

namespace Exp.L2.Generic

open Classical Kanon

/-- The language without its extensible helpers, for their cases (generated). -/
def langBase : XMod.Lang sem where
  Kind := Kind
  mk := Term.mk
  tbool := .TBool
  litK := .BLit
  notK := .BNot
  iteK := .BIte
  eqK := .BEq
  vb := .bool
  db := Val.toBool
  sure_neq := fun _ _ => false
  ty_mk := fun _ _ => rfl
  WT_lit := fun _ _ => Iff.rfl
  WT_not := fun _ _ => Iff.rfl
  WT_ite := fun _ _ _ _ => Iff.rfl
  WT_eq := fun _ _ _ => Iff.rfl
  ev_lit := fun _ _ _ => rfl
  ev_not := fun _ _ _ => rfl
  ev_ite := fun _ _ _ _ _ => rfl
  ev_eq := fun _ _ _ _ => rfl
  db_vb := fun _ => rfl
  vb_db := fun _ _ h => by simpa using h
  ev_bool := fun ρ t v w h e => ev_bool ρ t v w h e
  sure_neq_sound := fun _ _ _ _ h => by cases h
  tint := .TInt
  ilitK := .ILit
  addK := .Add
  ltK := .Lt
  ofBoolK := .OfBool
  vi := .int
  di := Val.toInt
  WT_ilit := fun _ _ => Iff.rfl
  WT_add := fun _ _ _ => Iff.rfl
  WT_lt := fun _ _ _ => Iff.rfl
  WT_ofBool := fun _ _ => Iff.rfl
  ev_ilit := fun _ _ _ => rfl
  ev_add := fun _ _ _ _ => rfl
  ev_lt := fun _ _ _ _ => rfl
  ev_ofBool := fun _ _ _ => rfl
  di_vi := fun _ => rfl
  vi_di := fun _ _ h => by simpa using h
  negK := .Neg
  WT_neg := fun _ _ => Iff.rfl
  ev_neg := fun _ _ _ => rfl

theorem sure_neq_sound (ρ : Env) (a b : Term) (u : Val) (h : L2.B.sure_neq a b = true)
    (e1 : ev ρ a = some u) (e2 : ev ρ b = some u) : False := by
  rcases L2.B.sure_neq_cases h with ⟨x, y, t, t', rfl, rfl, hxy⟩ | ⟨x, y, t, t', rfl, rfl, hxy⟩
  · exact BMod.sure_neq.bools (L := langBase.toI.toB) (ρ := ρ) (t := t) (t' := t') hxy e1 e2
  · exact IMod.B_sure_neq.ints (L := langBase.toI) (ρ := ρ) (t := t) (t' := t') hxy e1 e2

/-- The language, for its modules `B` and `I` (generated). -/
def lang : XMod.Lang sem := {
  langBase with
  sure_neq := L2.B.sure_neq
  sure_neq_sound := fun ρ a b u h _ _ _ e1 e2 => sure_neq_sound ρ a b u h e1 e2 }

def Ops.toX (O : Ops) : XMod.Ops lang :=
  { not_ := O.not_, ite := O.ite, eq := O.eq, tag_le := O.tag_le, add := O.add, lt := O.lt,
    of_bool := O.of_bool, neg := O.neg }

theorem Ops.Sound.toX {O : Ops} (hO : O.Sound) : (Ops.toX O).Sound :=
  { not_ := hO.not_, ite := hO.ite, eq := hO.eq, add := hO.add, lt := hO.lt,
    of_bool := hO.of_bool, neg := hO.neg }

theorem B.not_.lit : B.not_.lit.Stmt := fun O hO => BMod.not_.lit lang.toI.toB
theorem B.not_.nn : B.not_.nn.Stmt := fun O hO => BMod.not_.nn lang.toI.toB
theorem B.not_.lt : B.not_.lt.Stmt := fun O hO => IMod.B_not_.lt lang.toI (Ops.toX O).toI (Ops.Sound.toX hO).toI
theorem B.not_.default : B.not_.default.Stmt := fun O hO => BMod.not_.default lang.toI.toB
theorem B.ite.true_ : B.ite.true_.Stmt := fun O hO => BMod.ite.true_ lang.toI.toB
theorem B.ite.same : B.ite.same.Stmt := fun O hO => BMod.ite.same lang.toI.toB
theorem B.ite.bool : B.ite.bool.Stmt := fun O hO => BMod.ite.bool lang.toI.toB
theorem B.ite.default : B.ite.default.Stmt := fun O hO _ _ _ => Sem.Refines.refl
theorem B.eq.ints : B.eq.ints.Stmt := fun O hO => IMod.B_eq.ints lang.toI
theorem B.eq.same : B.eq.same.Stmt := fun O hO => BMod.eq.same lang.toI.toB
theorem B.eq.neq : B.eq.neq.Stmt := fun O hO => BMod.eq.neq lang.toI.toB
theorem B.eq.lits : B.eq.lits.Stmt := fun O hO => BMod.eq.lits lang.toI.toB
theorem B.eq.default : B.eq.default.Stmt := fun O hO => BMod.eq.default lang.toI.toB (Ops.toX O).toI.toB
theorem I.add.lits : I.add.lits.Stmt := fun O hO => IMod.add.lits lang.toI
theorem I.add.zero : I.add.zero.Stmt := fun O hO => IMod.add.zero lang.toI
theorem I.add.ite : I.add.ite.Stmt := fun O hO => IMod.add.ite lang.toI (Ops.toX O).toI (Ops.Sound.toX hO).toI
theorem I.add.negself : I.add.negself.Stmt := fun O hO => XMod.I_add.negself lang
theorem X.neg.lit : X.neg.lit.Stmt := fun O hO => XMod.neg.lit lang
theorem X.neg.nn : X.neg.nn.Stmt := fun O hO => XMod.neg.nn lang
theorem X.neg.default : X.neg.default.Stmt := fun O hO _ => Sem.Refines.refl
theorem I.add.default : I.add.default.Stmt := fun O hO => IMod.add.default lang.toI (Ops.toX O).toI
theorem I.lt.lits : I.lt.lits.Stmt := fun O hO => IMod.lt.lits lang.toI
theorem I.lt.same : I.lt.same.Stmt := fun O hO => IMod.lt.same lang.toI
theorem I.lt.ofbool : I.lt.ofbool.Stmt := fun O hO => IMod.lt.ofbool lang.toI
theorem I.lt.default : I.lt.default.Stmt := fun O hO _ _ => Sem.Refines.refl
theorem I.of_bool.true_ : I.of_bool.true_.Stmt := fun O hO => IMod.of_bool.true_ lang.toI
theorem I.of_bool.false_ : I.of_bool.false_.Stmt := fun O hO => IMod.of_bool.false_ lang.toI
theorem I.of_bool.default : I.of_bool.default.Stmt := fun O hO _ => Sem.Refines.refl

theorem steps_sound (O : Ops) (hO : O.Sound) :
    (∀ v, Refines (L2.B.not_.spec v) (L2.B.not_.step O v)) ∧
    (∀ g a b, Refines (L2.B.ite.spec g a b) (L2.B.ite.step O g a b)) ∧
    (∀ a b, Refines (L2.B.eq.spec a b) (L2.B.eq.step O a b)) ∧
    (∀ a b, Refines (L2.I.add.spec a b) (L2.I.add.step O a b)) ∧
    (∀ a b, Refines (L2.I.lt.spec a b) (L2.I.lt.step O a b)) ∧
    (∀ a, Refines (L2.I.of_bool.spec a) (L2.I.of_bool.step O a)) ∧
    (∀ a, Refines (L2.X.neg.spec a) (L2.X.neg.step O a)) :=
  ⟨L2.B.not_.step_sound B.not_.lit B.not_.nn B.not_.lt B.not_.default O hO,
   L2.B.ite.step_sound B.ite.true_ B.ite.same B.ite.bool B.ite.default O hO,
   L2.B.eq.step_sound B.eq.ints B.eq.same B.eq.neq B.eq.lits B.eq.default O hO,
   L2.I.add.step_sound I.add.lits I.add.zero I.add.ite I.add.negself I.add.default O hO,
   L2.I.lt.step_sound I.lt.lits I.lt.same I.lt.ofbool I.lt.default O hO,
   L2.I.of_bool.step_sound I.of_bool.true_ I.of_bool.false_ I.of_bool.default O hO,
   L2.X.neg.step_sound X.neg.lit X.neg.nn X.neg.default O hO⟩

end Exp.L2.Generic
