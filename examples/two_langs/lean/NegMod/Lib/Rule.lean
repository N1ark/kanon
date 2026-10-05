import NegMod.Lifts
import NumMod.Lib.Rule

/-!
# The arms of the neg module

`kanon_neg` is `kanon_num` (`NumMod.Lib.Rule`) with the typing and the
evaluation of `Neg`: it proves the arms of `neg` and the arm that the module
adds to the sums of the num module (`a + Neg a`).
-/

namespace NegMod

open Kanon

/-- `kanon_num`, with `Neg`. -/
macro "kanon_neg" : tactic => `(tactic| (
  intro _
  intros
  (try simp only [decide_eq_true_eq] at *)
  (try subst_vars)
  all_goals (try kanon_lift_body)
  all_goals (try simp only [kanon_spec])
  all_goals first
    | kanon_refl
    | (refine Kanon.Sem.Refines.intro ?_ ?_
       · intro w
         (try kanon_num_simp at w ⊢)
         (try simp only [NegMod.Syntax.WT_Neg] at w ⊢)
         (try kanon_num_simp at w ⊢)
         (try kanon_split)
         (try subst_vars)
         (try grind)
       · intro ρ v w w' e
         (try kanon_num_simp at w w' e ⊢)
         (try simp only [NegMod.Syntax.WT_Neg, NegMod.Sem.ev_Neg, NegMod.negV] at w w' e ⊢)
         (try kanon_num_simp at w w' e ⊢)
         (try kanon_split)
         kanon_num_cases
         all_goals (try kanon_num_val at e ⊢)
         kanon_num_cases
         all_goals (try kanon_num_val at e ⊢)
         all_goals (try subst e)
         all_goals (simp_all [NumMod.op2, NumMod.Sem.toInt_vint, NumMod.Sem.vint_eq_iff]
           <;> omega))))

attribute [kanon_tactic "kanon_neg"] Neg.neg.spec Syntax


end NegMod
