import EvenMod.Sem
import NegMod.Sem
import MixMod.Syntax

/-!
# What the mix module needs of the semantics of a language

Nothing more than what the even and neg modules need: its rule is about their
nodes and those of the num module, which both use.
-/

namespace MixMod

/-- What the mix module needs of the semantics `S` of a language: nothing. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    {LBool : KanonBool.Syntax B} {LNum : NumMod.Syntax B LBool}
    {LEven : EvenMod.Syntax B LBool LNum} {LNeg : NegMod.Syntax B LBool LNum}
    (L : Syntax B LBool LNum LEven LNeg) [KanonBool.Sem LBool] [NumMod.Sem LNum]
    [EvenMod.Sem LEven] [NegMod.Sem LNeg] : Prop where

end MixMod
