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

theorem Refines.unop {op : Unop} {a a' : Term} {t : Ty} (ha : Refines a a') :
    Refines (.mk (.Unop op a) t) (.mk (.Unop op a') t) := by
  cases op; exact Lang.refines_not (L := boolLang) ha

theorem Refines.binop {op : Binop} {a a' b b' : Term} {t : Ty} (ha : Refines a a')
    (hb : Refines b b') : Refines (.mk (.Binop op a b) t) (.mk (.Binop op a' b') t) := by
  cases op
  · exact Lang.refines_and (L := boolLang) ha hb
  · exact Lang.refines_or (L := boolLang) ha hb
  · exact Lang.refines_eq (L := boolLang) ha hb

theorem Refines.triop {op : Triop} {a a' b b' c c' : Term} {t t' : Ty} (ha : Refines a a')
    (hb : Refines b b') (hc : Refines c c') :
    Refines (.mk (.Triop op a b c) t) (.mk (.Triop op a' b' c') t') := by
  cases op; exact Lang.refines_ite (L := boolLang) ha hb hc fun _ => Ty.eq_all _ _

attribute [kanon_congr_lemma] Refines.unop Refines.binop Refines.triop

end BoolExample
