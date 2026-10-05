import EvenMod.Statements.Even.rem2
import EvenMod.Lib.Rule

/-!
# The arm `Ev z → 0` of `rem2`

It holds of even literals only: the typing of `Rem2 (Ev z)` gives that of its
operand, and with it the invariant of its sort (`WT_Ev`), which means that `z`
is even (`Sem.even_inv_Ev`). The lemmas of the num module (`NumMod.Sem.ev_Num`,
`NumMod.Sem.toInt_vint`) apply as they are, over the interface `LNum` that is a
parameter of that of this module.
-/

namespace EvenMod

open Kanon

@[kanon_arm] theorem rem2_lit : Even.rem2.r_lit.main.Stmt := by
  intro S _ _ B LBool LNum L _ _ _ O hO z t
  refine Sem.Refines.intro (fun w => ?_) (fun ρ v w _ e => ?_)
  · simp [Even.rem2.spec, L.WT_Rem2, LNum.WT_Num, B.ty_node] at w ⊢
  · simp only [Even.rem2.spec, L.WT_Rem2, L.WT_Ev, Sem.even_inv_Ev] at w
    simp only [Even.rem2.spec, Sem.ev_Rem2, Sem.ev_Ev, rem2V, NumMod.Sem.toInt_vint,
      Option.bind_some, Option.map_some, Option.some.injEq, w.2.2] at e
    rw [NumMod.Sem.ev_Num, ← e]

end EvenMod
