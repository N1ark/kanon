import KanonCore.Proof
import BoolExample.Statements
import BoolExample.Bool

/-!
# Refinement by congruence

The congruence of refinement, from that of the nodes of the bool module in
Kanon's library (`Kanon.BoolMod.Lang.refines_and`, …), with which `kanon_congr`
(Kanon's) proves the monotonicity of the specs (`Lifts.lean`): the result of a
rule function called on terms that refine `a` and `b` refines its spec on `a`
and `b`.
-/

namespace BoolExample

open Kanon BoolMod

theorem Refines.op1 {op : Op1} {a a' : Term} {t : Ty} (ha : Refines a a') :
    Refines (.mk (.Op1 op a) t) (.mk (.Op1 op a') t) := by
  cases op; exact Lang.refines_not (L := boolLang) ha

theorem Refines.op2 {op : Op2} {a a' b b' : Term} {t : Ty} (ha : Refines a a')
    (hb : Refines b b') : Refines (.mk (.Op2 op a b) t) (.mk (.Op2 op a' b') t) := by
  cases op
  · exact Lang.refines_and (L := boolLang) ha hb
  · exact Lang.refines_or (L := boolLang) ha hb
  · exact Lang.refines_eq (L := boolLang) ha hb

theorem Refines.op3 {op : Op3} {a a' b b' c c' : Term} {t t' : Ty} (ha : Refines a a')
    (hb : Refines b b') (hc : Refines c c') :
    Refines (.mk (.Op3 op a b c) t) (.mk (.Op3 op a' b' c') t') := by
  cases op; exact Lang.refines_ite (L := boolLang) ha hb hc fun _ => Ty.eq_all _ _

attribute [kanon_congr_lemma] Refines.op1 Refines.op2 Refines.op3

end BoolExample
