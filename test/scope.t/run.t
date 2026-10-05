The names of functions, rules, primitives and constants are scoped by module: a
module is a file (`int.knl` and `int.kn` are the module `Int`), and the name
`add` of `int.kn` is `Int.add` from the other modules. An `Int.add` and a
`Bitvec.add` live in the same language. The nodes, sorts and types stay global.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > [@@@ocaml_rules "Rules"]
  > use "int"
  > use "bitvec"
  > KN
  $ cat > int.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > node IAdd : TInt -> TInt -> TInt [@comm] [@fold add] [@unit 0]
  > notation Int
  > infix "+" = IAdd, plus
  > KN
  $ cat > int.kn <<'KN'
  > fn add (x y : int) : int = x + y
  > rule plus : IAdd (v1, v2)
  > KN

Inside its module a name is plain (`add` in the `[@fold]` of int.knl, and
`plus` in its `infix`), and from another module it is qualified, with a dot and
no space:

  $ cat > bitvec.knl <<'KN'
  > sort TBv of nat
  > node Bv of int * nat (v, n) : TBv n
  > node BAdd : TBv n -> TBv n -> TBv n
  > KN
  $ cat > bitvec.kn <<'KN'
  > prim wrap : int -> int -> int
  > fn add (n : nat) (x y : int) : int = wrap n (Int.add x y)
  > rule badd : BAdd (v1, v2)
  > KN

In OCaml, the rules have the structure of the modules: a module per Kanon
module, with the plain names, and the primitives stay in the module of the
primitives. The functions are defined together, since a function may call one
of a module that comes after (an `extend` does), in `Kanon_flat`, by their flat
name (the module in lowercase, an underscore, and the name), which the modules
alias:

  $ kanon ocaml lang.knl | grep "^module [IB]\|^  let [a-z]* = Kanon_flat\|^  let.*bitvec_add\|(Prims"
    let[@inline] bitvec_add (n : Z.t) (x : Z.t) (y : Z.t) : Z.t =
        (Prims.wrap n (int_add x y))
  module Int = struct
    let add = Kanon_flat.int_add
    let plus = Kanon_flat.int_plus
  module Bitvec = struct
    let add = Kanon_flat.bitvec_add
    let badd = Kanon_flat.bitvec_badd

The typed interface has the same modules, and Lean the names qualified by their
module (its structures have flat fields):

  $ kanon ocaml-typed lang.knl | grep "val plus\|val badd\|^    module"
      val plus : [< Tag.tint ] t -> [< Tag.tint ] t -> [> Tag.tint ] t
      val badd : [< Tag.tbv ] t -> [< Tag.tbv ] t -> [> Tag.tbv ] t
  $ kanon lean-model lang.knl | grep "def Int.add\|def Bitvec.add\|^    int_plus :\|^    bitvec_badd :"
  def Int.add (x : Int) (y : Int) : Int :=
  def Bitvec.add (n : Int) (x : Int) (y : Int) : Int :=
      int_plus := fun v1 v2 => Int.plus.spec v1 v2,
      bitvec_badd := fun v1 v2 => Bitvec.badd.spec v1 v2 }
      int_plus := Int.plus.step O,
      bitvec_badd := Bitvec.badd.step O }

A plain name is the one of the module of the file where it is written, never
that of a module that it uses: the hint names the other module.

  $ cat > bad.kn <<'KN'
  > fn bad (x y : int) : int = add x y
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:27: unknown function add: Int.add is declared in another module, write it qualified
  [1]
  $ cat > bad.kn <<'KN'
  > fn bad (x y : int) : int = Int.sub x y
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:27: unknown function Int.sub
  [1]

A variable cannot have the name of a function of its module, but may have that
of a function of another module:

  $ cat > ok.kn <<'KN'
  > fn ok (add : int) : int = add
  > KN
  $ kanon ocaml lang.knl ok.kn | grep "ok_ok"
    let[@inline] ok_ok (add : Z.t) : Z.t = add
    let ok = Kanon_flat.ok_ok
  $ cat > bad.kn <<'KN'
  > fn add (x : int) : int = let bad (x : int) = x in x
  > fn bad2 (add : int) : int = add
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:2:9: add shadows a global function
  [1]

`extend` names its target qualified, and its cases are written in the module that
extends, so the names they call are its own, or qualified:

  $ cat > ext.kn <<'KN'
  > fn double (x : int) : int = Int.add x x
  > extend rule Int.plus =
  >   | same: x + x -> Int (double 1)
  > KN
  $ kanon ocaml lang.knl ext.kn | grep "ext_double"
    let[@inline] ext_double (x : Z.t) : Z.t = (int_add x x)
          (node (Int ((ext_double Z.one))) TInt)
    let double = Kanon_flat.ext_double
  $ sed -i 's/Int.plus/plus/' ext.kn
  $ kanon ocaml lang.knl ext.kn
  ext.kn:2:12: extend Ext.plus: no rule Ext.plus is defined before
  [1]
  $ sed -i 's/double 1/Int.add 1 1/; s/Int.add x x/Int.add x 1/' ext.kn
  $ sed -i 's/extend rule plus/extend rule Int.plus/' ext.kn
  $ kanon ocaml lang.knl ext.kn > /dev/null

A module cannot define a name that Kanon provides, and two primitives of
different modules have the same name in the module of the primitives:

  $ cat > bad.kn <<'KN'
  > fn type_of (x : int) : int = x
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:3: type_of is built in
  [1]
  $ cat > bad.kn <<'KN'
  > prim wrap : int -> int
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:5: Bitvec.wrap and Bad.wrap are both the primitive wrap
  [1]
