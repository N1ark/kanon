import CfgMod.Syntax

/-! The cfg module has data types only: it needs nothing of the semantics of a
language. -/

namespace CfgMod

/-- What the cfg module needs of the semantics `S` of a language: nothing. -/
class Sem {S : Kanon.Sem} [DecidableEq S.Term] [DecidableEq S.Ty] {B : Kanon.Base S}
    (L : Syntax B) where

end CfgMod
