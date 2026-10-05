import L4.Interface.Cfg

/-! The language, for the cfg module, which needs nothing of its semantics. -/

namespace L4

open Classical Kanon

/-- The cfg module needs nothing. -/
instance cfgSem : CfgMod.Sem (S := sem) cfgSyntax := {}

end L4
