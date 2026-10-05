import EvenMod.Lifts

/-!
# The default proof of the arms of the even module

The default arm of `rem2` is the spec itself (`kanon_refl`); its other arm is
proved by hand (`Proofs/Even/rem2.lean`).
-/

namespace EvenMod

macro "kanon_even" : tactic => `(tactic| (intro _; intros; simp only [kanon_spec]; kanon_refl))

attribute [kanon_tactic "kanon_even"] Even.rem2.spec Syntax

end EvenMod
