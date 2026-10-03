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
    ((bv_div false x y).ty = TBitVector 8);
  check "the rules apply" (bv_div false x x == Sub_prims.one (Z.of_int 8));
  check "no rule" ((bv_div false x y).kind = Op2 (Div false, x, y));
  check "ult" (bv_ult x x == Sub_prims.one Z.zero);
  (* a term of TZero, erased, is a divisor like another: nothing is checked *)
  check "destructors"
    (as_div (bv_div true x y) = Some (true, x, y)
    && is_zero (node (Zero 8) (TBitVector 8)));
  check "the subsorts have no destructor"
    (as_tbitvector x.ty = Some 8
    && is_tbool (node (Zero 8) (TBitVector 8)).ty = false)

(* The typed interface: [Ghost] gives the phantom types and the escape hatches,
   the rules give the smart constructors, and the leaves are written by hand. *)

module Typed : Sub_typed.S = struct
  include Sub_typed.Ghost
  include Sub_rules

  let mk_bv v n = node (BitVec (v, n)) (TBitVector n)
  let mk_zero n = node (Zero n) (TBitVector n)
end

let () =
  let open Typed in
  let x = mk_bv (Z.of_int 3) 8 and z = mk_zero 8 in
  (* the escape hatches do not change the term *)
  check "cast" (cast x == x && untyped (cast x) == untyped x);
  check "type_" (type_ (untyped x) == x);
  check "sorts" (untype_type (t_bitvector 8) = TBitVector 8);
  check "type_type" (type_type (TBitVector 8) = t_bitvector 8);
  (* a zero is a bit-vector, and a divisor once cast *)
  let d = bv_div false x (cast z) in
  check "typed rule"
    (untyped d == Sub_rules.bv_div false (untyped x) (untyped z));
  check "typed destructors"
    (as_div d = Some (false, x, cast z) && is_div d && as_zero z = Some 8);
  check "sorts of the destructors" (as_tbitvector (t_bitvector 8) = Some 8)
