import Exp.L1.Step
import Exp.Generic.IMod

/-! Option B: language 1 instantiates the interfaces of its modules, and its
arms are the generic theorems. -/

set_option linter.unusedVariables false

noncomputable section

namespace Exp.L1.Generic

open Classical Kanon

/-- The language without its extensible helpers, for their cases (generated). -/
def langBase : IMod.Lang sem where
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

theorem sure_neq_sound (ρ : Env) (a b : Term) (u : Val) (h : L1.B.sure_neq a b = true)
    (e1 : ev ρ a = some u) (e2 : ev ρ b = some u) : False := by
  rcases L1.B.sure_neq_cases h with ⟨x, y, t, t', rfl, rfl, hxy⟩ | ⟨x, y, t, t', rfl, rfl, hxy⟩
  · exact BMod.sure_neq.bools (L := langBase.toB) (ρ := ρ) (t := t) (t' := t') hxy e1 e2
  · exact IMod.B_sure_neq.ints (L := langBase) (ρ := ρ) (t := t) (t' := t') hxy e1 e2

/-- The language, for its modules `B` and `I` (generated). -/
def lang : IMod.Lang sem := {
  langBase with
  sure_neq := L1.B.sure_neq
  sure_neq_sound := fun ρ a b u h _ _ _ e1 e2 => sure_neq_sound ρ a b u h e1 e2 }

def Ops.toI (O : Ops) : IMod.Ops lang :=
  { not_ := O.not_, ite := O.ite, eq := O.eq, tag_le := O.tag_le, add := O.add, lt := O.lt,
    of_bool := O.of_bool }

theorem Ops.Sound.toI {O : Ops} (hO : O.Sound) : (Ops.toI O).Sound :=
  { not_ := hO.not_, ite := hO.ite, eq := hO.eq, add := hO.add, lt := hO.lt,
    of_bool := hO.of_bool }

theorem B.not_.lit : B.not_.lit.Stmt := fun O hO => BMod.not_.lit lang.toB
theorem B.not_.nn : B.not_.nn.Stmt := fun O hO => BMod.not_.nn lang.toB
theorem B.not_.lt : B.not_.lt.Stmt := fun O hO => IMod.B_not_.lt lang (Ops.toI O) (Ops.Sound.toI hO)
theorem B.not_.default : B.not_.default.Stmt := fun O hO => BMod.not_.default lang.toB
theorem B.ite.true_ : B.ite.true_.Stmt := fun O hO => BMod.ite.true_ lang.toB
theorem B.ite.same : B.ite.same.Stmt := fun O hO => BMod.ite.same lang.toB
theorem B.ite.bool : B.ite.bool.Stmt := fun O hO => BMod.ite.bool lang.toB
theorem B.ite.default : B.ite.default.Stmt := fun O hO _ _ _ => Sem.Refines.refl
theorem B.eq.ints : B.eq.ints.Stmt := fun O hO => IMod.B_eq.ints lang
theorem B.eq.same : B.eq.same.Stmt := fun O hO => BMod.eq.same lang.toB
theorem B.eq.neq : B.eq.neq.Stmt := fun O hO => BMod.eq.neq lang.toB
theorem B.eq.lits : B.eq.lits.Stmt := fun O hO => BMod.eq.lits lang.toB
theorem B.eq.default : B.eq.default.Stmt := fun O hO => BMod.eq.default lang.toB (Ops.toI O).toB
theorem I.add.lits : I.add.lits.Stmt := fun O hO => IMod.add.lits lang
theorem I.add.zero : I.add.zero.Stmt := fun O hO => IMod.add.zero lang
theorem I.add.ite : I.add.ite.Stmt := fun O hO => IMod.add.ite lang (Ops.toI O) (Ops.Sound.toI hO)
theorem I.add.default : I.add.default.Stmt := fun O hO => IMod.add.default lang (Ops.toI O)
theorem I.lt.lits : I.lt.lits.Stmt := fun O hO => IMod.lt.lits lang
theorem I.lt.same : I.lt.same.Stmt := fun O hO => IMod.lt.same lang
theorem I.lt.ofbool : I.lt.ofbool.Stmt := fun O hO => IMod.lt.ofbool lang
theorem I.lt.default : I.lt.default.Stmt := fun O hO _ _ => Sem.Refines.refl
theorem I.of_bool.true_ : I.of_bool.true_.Stmt := fun O hO => IMod.of_bool.true_ lang
theorem I.of_bool.false_ : I.of_bool.false_.Stmt := fun O hO => IMod.of_bool.false_ lang
theorem I.of_bool.default : I.of_bool.default.Stmt := fun O hO _ => Sem.Refines.refl

theorem steps_sound (O : Ops) (hO : O.Sound) :
    (∀ v, Refines (L1.B.not_.spec v) (L1.B.not_.step O v)) ∧
    (∀ g a b, Refines (L1.B.ite.spec g a b) (L1.B.ite.step O g a b)) ∧
    (∀ a b, Refines (L1.B.eq.spec a b) (L1.B.eq.step O a b)) ∧
    (∀ a b, Refines (L1.I.add.spec a b) (L1.I.add.step O a b)) ∧
    (∀ a b, Refines (L1.I.lt.spec a b) (L1.I.lt.step O a b)) ∧
    (∀ a, Refines (L1.I.of_bool.spec a) (L1.I.of_bool.step O a)) :=
  ⟨L1.B.not_.step_sound B.not_.lit B.not_.nn B.not_.lt B.not_.default O hO,
   L1.B.ite.step_sound B.ite.true_ B.ite.same B.ite.bool B.ite.default O hO,
   L1.B.eq.step_sound B.eq.ints B.eq.same B.eq.neq B.eq.lits B.eq.default O hO,
   L1.I.add.step_sound I.add.lits I.add.zero I.add.ite I.add.default O hO,
   L1.I.lt.step_sound I.lt.lits I.lt.same I.lt.ofbool I.lt.default O hO,
   L1.I.of_bool.step_sound I.of_bool.true_ I.of_bool.false_ I.of_bool.default O hO⟩

end Exp.L1.Generic
