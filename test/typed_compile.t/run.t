The typed interface compiles, and rejects what the subsorts forbid. In this
language, TNonzero and TZero are subsorts of TBitVector, with the tags
`tnonzero` and `tzero`, and the language is in two modules, bitvec and cmp. The
types, the rules and the interface are generated, and the interface is
implemented by the generated `Derived` and the leaf nodes, which are written by
hand.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "Sub_types"]
  > [@@@ocaml_prims "Sub_prims"]
  > [@@@ocaml_rules "Sub_rules"]
  > use "bitvec"
  > use "cmp"
  > KN
  $ cat > bitvec.knl <<'KN'
  > sort TBitVector of nat [@get size]
  > subsort TNonzero of nat : TBitVector n
  > subsort TZero of nat : TBitVector n
  > node BitVec of int * nat (v, n) : TBitVector n [@ctor mk_bv]
  > node Zero of nat (n) : TZero n [@ctor mk_zero]
  > node Div : TBitVector n -> TNonzero n -> TBitVector n
  > KN
  $ cat > bitvec.kn <<'KN'
  > prim size : t -> int
  > rule bv_div : Div (v1, v2)
  > KN
  $ cat > cmp.knl <<'KN'
  > sort TBool
  > node Ult : TBitVector n -> TBitVector n -> TBool
  > KN
  $ cat > cmp.kn <<'KN'
  > rule bv_ult : Ult (v1, v2)
  > KN
  $ cat > sub_prims.ml <<'ML'
  > let size (t : Sub_types.t) =
  >   match t.ty with Sub_types.TBitVector n -> Z.of_int n | _ -> Z.zero
  > ML
  $ kanon ocaml-types lang.knl > sub_types.ml
  $ kanon ocaml lang.knl > sub_rules.ml
  $ kanon ocaml-typed lang.knl > sub_typed.ml
  $ cat > impl.ml <<'ML'
  > module Typed : Sub_typed.S = struct
  >   include Sub_typed.Derived
  > 
  >   module Bitvec = struct
  >     include Sub_typed.Derived.Bitvec
  > 
  >     let mk_bv v n = Sub_types.node (BitVec (v, n)) (TBitVector n)
  >     let mk_zero n = Sub_types.node (Zero n) (TBitVector n)
  >   end
  > end
  > ML
  $ ocamlfind ocamlc -package zarith -c sub_types.ml sub_prims.ml sub_rules.ml sub_typed.ml impl.ml

A divisor that is a bit-vector is not known to be non-zero, nor is a zero. A
`cast` says that it is non-zero, and is the identity:

  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = Bitvec.bv_div x x
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TBitVector, `TZero
  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let _ = Bitvec.bv_div (Bitvec.mk_bv Z.one 8) (Bitvec.mk_zero 8)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TZero
  $ cat > good.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let ok = Bitvec.bv_div x (cast x)
  > let () = assert (untyped ok == untyped (Bitvec.bv_div x (type_ (untyped x))))
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c good.ml

A term of a subsort is accepted where its parent is expected, in another module
too:

  $ cat > good.ml <<'ML'
  > open Impl.Typed
  > let z = Bitvec.mk_zero 8
  > let _ = Bitvec.bv_div z (cast z)
  > let _ = Cmp.bv_ult z z
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c good.ml

A term of another sort is not a bit-vector, and an untyped term is not a typed
one: `S` hides that the typed terms are the untyped ones.

  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = Cmp.bv_ult x (untyped x)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'This expression has type.*'
  This expression has type Impl.Typed.raw = Sub_types.t
  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = Cmp.bv_ult x (Cmp.bv_ult x x)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TBool

The tags are plain polymorphic variants, whose types may be joined to make a
group of tags, which is the user's:

  $ cat > group.ml <<'ML'
  > type scalar = [ Sub_typed.Tag.tbitvector | Sub_typed.Tag.tbool ]
  > open Impl.Typed
  > let is_node (t : [< scalar ] t) = Bitvec.is_div t || Cmp.is_ult t
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = is_node x && is_node (Cmp.bv_ult x x)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c group.ml
