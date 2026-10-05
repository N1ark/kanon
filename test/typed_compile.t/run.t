The typed interface compiles, and rejects what the subsorts forbid. In this
language, TNonzero and TZero are subsorts of TBitVector, with the tags
`tnonzero` and `tzero`, and the language is in two modules, bitvec and cmp. The
types, the rules and the interface are generated, and the interface is
implemented by the generated `Derived`, which has no constructor for the leaf
nodes: they are added by hand.

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
  > node BitVec of int * nat (v, n) : TBitVector n
  > node Zero of nat (n) : TZero n
  > node Div : TBitVector n -> TNonzero n -> TBitVector n
  > KN
  $ cat > bitvec.kn <<'KN'
  > prim size : t -> int
  > rule div : Div (v1, v2)
  > KN
  $ cat > cmp.knl <<'KN'
  > sort TBool
  > node Ult : TBitVector n -> TBitVector n -> TBool
  > KN
  $ cat > cmp.kn <<'KN'
  > rule ult : Ult (v1, v2)
  > KN
  $ cat > sub_prims.ml <<'ML'
  > let size (t : Sub_types.t) =
  >   match t.ty with Sub_types.TBitVector n -> Z.of_int n | _ -> Z.zero
  > ML
  $ kanon ocaml-types lang.knl > sub_types.ml
  $ kanon ocaml lang.knl > sub_rules.ml
  $ kanon ocaml-typed lang.knl > sub_typed.ml
  $ cat > impl.ml <<'ML'
  > module Typed = struct
  >   include (Sub_typed.Derived : Sub_typed.S)
  > 
  >   module Bitvec = struct
  >     include Bitvec
  > 
  >     let mk_bv v n : [> Sub_typed.Tag.tbitvector ] t =
  >       type_ (Sub_types.node (BitVec (v, n)) (TBitVector n))
  > 
  >     let mk_zero n : [> Sub_typed.Tag.tzero ] t =
  >       type_ (Sub_types.node (Zero n) (TBitVector n))
  >   end
  > end
  > ML
  $ ocamlfind ocamlc -package zarith -c sub_types.ml sub_prims.ml sub_rules.ml sub_typed.ml impl.ml

A divisor that is a bit-vector is not known to be non-zero, nor is a zero. A
`cast` says that it is non-zero, and is the identity:

  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = Bitvec.div x x
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TBitVector, `TZero
  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let _ = Bitvec.div (Bitvec.mk_bv Z.one 8) (Bitvec.mk_zero 8)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'does not allow.*'
  does not allow tag(s) `TZero
  $ cat > good.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let ok = Bitvec.div x (cast x)
  > let () = assert (untyped ok == untyped (Bitvec.div x (type_ (untyped x))))
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c good.ml

A term of a subsort is accepted where its parent is expected, in another module
too:

  $ cat > good.ml <<'ML'
  > open Impl.Typed
  > let z = Bitvec.mk_zero 8
  > let _ = Bitvec.div z (cast z)
  > let _ = Cmp.ult z z
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c good.ml

A term of another sort is not a bit-vector, and an untyped term is not a typed
one: `S` hides that the typed terms are the untyped ones.

  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = Cmp.ult x (untyped x)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c bad.ml 2>&1 | grep -o 'This expression has type.*'
  This expression has type Impl.Typed.raw = Sub_types.t
  $ cat > bad.ml <<'ML'
  > open Impl.Typed
  > let x = Bitvec.mk_bv Z.one 8
  > let _ = Cmp.ult x (Cmp.ult x x)
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
  > let _ = is_node x && is_node (Cmp.ult x x)
  > ML
  $ ocamlfind ocamlc -package zarith -I . -c group.ml

The typed module is the module of the rules, seen through `S`: a call through
`Typed` is the call of the rules, on the same term. The interface checks itself
against the rules (`module _ : S = Derived`, in the generated file), and
`Derived` is the rules and the phantom types, with no function of its own:

  $ kanon ocaml-typed lang.knl | sed -n '/^module Derived/,/^end/p' | grep -c "^  let\[@inline\]"
  5
  $ kanon ocaml-typed lang.knl | grep "include Sub\|module _"
    include Sub_rules
  module _ : S = Derived
  $ cat > run.ml <<'ML'
  > let () =
  >   let open Impl.Typed in
  >   let x = Bitvec.mk_bv (Z.of_int 5) 8 in
  >   let d = Bitvec.div x (cast x) in
  >   assert (untyped d == Sub_rules.Bitvec.div (untyped x) (untyped x));
  >   assert (untyped (Cmp.ult x x) == Sub_rules.Cmp.ult (untyped x) (untyped x));
  >   print_endline "ok"
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg sub_types.ml sub_prims.ml sub_rules.ml sub_typed.ml impl.ml run.ml -o run.exe
  $ ./run.exe
  ok
