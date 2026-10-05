import KanonCore.Sem

/-! Value operations shared by every language (as `KanonCore.BoolMod.Val`):
parametrised by the injections (`vb`, `vi`) and decoders (`db`, `di`) of the
booleans and integers among the values of a language. -/

namespace Exp

open Classical

variable {V : Type}

def pnot (vb : Bool → V) (db : V → Option Bool) (a : Option V) : Option V :=
  a.bind fun x => (db x).map fun b => vb (!b)

def pite (db : V → Option Bool) (g a b : Option V) : Option V :=
  g.bind fun x => (db x).bind fun c => if c then a else b

noncomputable def peq (vb : Bool → V) (a b : Option V) : Option V :=
  a.bind fun x => b.map fun y => vb (decide (x = y))

def padd (vi : Int → V) (di : V → Option Int) (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (di x).bind fun m => (di y).map fun n => vi (m + n)

def plt (vb : Bool → V) (di : V → Option Int) (a b : Option V) : Option V :=
  a.bind fun x => b.bind fun y => (di x).bind fun m => (di y).map fun n => vb (decide (m < n))

def pofbool (vi : Int → V) (db : V → Option Bool) (a : Option V) : Option V :=
  a.bind fun x => (db x).map fun b => vi (if b then 1 else 0)

def pneg (vi : Int → V) (di : V → Option Int) (a : Option V) : Option V :=
  a.bind fun x => (di x).map fun m => vi (-m)

end Exp
