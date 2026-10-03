The typed interface compiles, and rejects what the subsorts forbid. In this
language, TNonzero and TZero are subsorts of TBitVector, with the tags
`tnonzero` and `tzero`. The types, the rules and the interface are generated,
and the implementation of the interface is the generated phantom types and
rules, and the leaf nodes, which are written by hand.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "Sub_types"]
  > [@@@ocaml_prims "Sub_prims"]
  > use "rules"
  > sort TBitVector of nat [@get size]
  > subsort TNonzero of nat : TBitVector n
  > subsort TZero of nat : TBitVector n
  > node BitVec of int * nat (v, n) : TBitVector n [@ctor mk_bv]
  > node Zero of nat (n) : TZero n [@ctor mk_zero]
  > node Div : TBitVector n -> TNonzero n -> TBitVector n
  > KN
  $ cat > rules.kn <<'KN'
  > prim size : t -> int
  > rule bv_div : Div (v1, v2)
  > KN
  $ cat > sub_prims.ml <<'ML'
  > let size (t : Sub_types.t) =
  >   match t.ty with Sub_types.TBitVector n -> Z.of_int n
  > ML
  $ kanon ocaml-types lang.knl > sub_types.ml
  $ kanon ocaml lang.knl > sub_rules.ml
  $ kanon ocaml-typed lang.knl > sub_typed.ml
  $ cat > impl.ml <<'ML'
  > module Typed : Sub_typed.S = struct
  >   include Sub_typed.Ghost
  >   include Sub_rules
  >   let mk_bv v n = Sub_types.node (BitVec (v, n)) (TBitVector n)
  >   let mk_zero n = Sub_types.node (Zero n) (TBitVector n)
  > end
  > ML
  $ ocamlfind ocamlc -package zarith -c sub_types.ml sub_prims.ml sub_rules.ml sub_typed.ml impl.ml

A divisor that is a bit-vector is not known to be non-zero, nor is a zero. A
`cast` says that it is non-zero, and is the identity:

  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = mk_bv Z.one 8
  > let _ = bv_div x x
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TBitVector, `TZero
  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let _ = bv_div (mk_bv Z.one 8) (mk_zero 8)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TZero
  $ cat > good.ml <<'ML'
  > open Impl.Typed
  > let x = mk_bv Z.one 8
  > let ok = bv_div x (cast x)
  > let () = assert (untyped ok == untyped (bv_div x (type_ (untyped x))))
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c good.ml

A term of a subsort is accepted where its parent is expected:

  $ cat > good.ml <<'ML'
  > open Impl.Typed
  > let z = mk_zero 8
  > let _ = bv_div z (cast z)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c good.ml
