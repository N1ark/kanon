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
  check "a zero is a divisor"
    ((bv_div true x (node (Zero 8) (TBitVector 8))).kind
    = Op2 (Div true, x, node (Zero 8) (TBitVector 8)))
