(* A subsort is its parent in OCaml: the terms of TZero are accepted wherever
   those of TBitVector are, and a node that mentions a subsort in its typing has
   the sort of the parent. *)

open Sub_types
open Sub_rules

let check name b = if not b then failwith ("test failed: " ^ name)

let () =
  let bv v = node (BitVec (Z.of_int v, 8)) (TBitVector 8) in
  let x = bv 3 and y = bv 5 in
  (* the subsorts are not in [ty] *)
  check "sort of a literal" (x.ty = TBitVector 8);
  check "a zero has the sort of its parent"
    ((node (Zero 8) (TBitVector 8)).ty = TBitVector 8);
  check "a division has the sort of its dividend"
    ((Sub_rules.bitvec_div false x y).ty = TBitVector 8);
  check "the rules apply"
    (Sub_rules.bitvec_div false x x == Sub_prims.one (Z.of_int 8));
  check "no rule" ((Sub_rules.bitvec_div false x y).kind = Op2 (Div false, x, y));
  check "ult" (Sub_rules.cmp_ult x x == Sub_prims.one Z.zero);
  (* a term of TZero, erased, is a divisor like another: nothing is checked *)
  check "destructors"
    (as_div (Sub_rules.bitvec_div true x y) = Some (true, x, y)
    && is_zero (node (Zero 8) (TBitVector 8)));
  check "the subsorts have no destructor"
    (as_tbitvector x.ty = Some 8
    && is_tbool (node (Zero 8) (TBitVector 8)).ty = false)

(* The typed interface, over the types and the rules above: [Sub_typed.S] is
   implemented by [Sub_typed.Derived], which has no constructor for the leaf
   nodes: [Typed] adds them, by hand, with [type_]. [S] makes the phantom types
   abstract: nothing here knows that a typed term is an untyped one, but the
   escape hatches. *)

module Typed = struct
  include (Sub_typed.Derived : Sub_typed.S)

  module Bitvec = struct
    include Bitvec

    let mk_bv v n : [> Sub_typed.Tag.tbitvector ] t =
      type_ (node (BitVec (v, n)) (TBitVector n))

    let mk_zero n : [> Sub_typed.Tag.tzero ] t =
      type_ (node (Zero n) (TBitVector n))
  end
end

(* The groups of tags are the user's: the tags are plain polymorphic variants,
   which may be joined with the tags of other sorts. *)
type bv_or_bool = [ Sub_typed.Tag.tbitvector | Sub_typed.Tag.tbool ]

let () =
  let open Typed in
  let x = Bitvec.mk_bv (Z.of_int 3) 8 and z = Bitvec.mk_zero 8 in
  (* the escape hatches do not change the term *)
  check "cast" (cast x == x && untyped (cast x) == untyped x);
  check "type_" (type_ (untyped x) == x);
  check "sorts"
    (untype_type (Bitvec.t_bitvector 8) = TBitVector 8
    && untype_type Cmp.t_bool = TBool);
  check "type_type" (type_type (TBitVector 8) = Bitvec.t_bitvector 8);
  (* a zero is a bit-vector, and a divisor once cast *)
  let d = Bitvec.div false x (cast z) in
  check "typed rule"
    (untyped d == Sub_rules.bitvec_div false (untyped x) (untyped z));
  let c = Cmp.ult x z in
  check "typed rule of another module"
    (untyped c == Sub_rules.cmp_ult (untyped x) (untyped z));
  check "typed destructors"
    (Bitvec.as_div d = Some (false, x, cast z)
    && Bitvec.is_div d
    && Bitvec.as_zero z = Some 8);
  check "sorts of the destructors"
    (Bitvec.as_tbitvector (Bitvec.t_bitvector 8) = Some 8);
  (* a function over a group of tags, which accepts the terms of each *)
  let describe (t : [< bv_or_bool ] t) =
    Bitvec.is_div t || Bitvec.is_bitvec t
  in
  check "a group of tags" (describe d && describe c = false)
