(* Runs the generated rules on a few terms. *)

let check name b = if not b then failwith ("test failed: " ^ name)

let () =
  let open Tiny_types in
  let open Tiny_rules in
  let int n = node (Int (Z.of_int n)) TInt in
  let x = node (Var "x") TInt and p = node (Var "p") TBool in
  check "hash-consing" (int 3 == int 3 && not (int 3 == int 4));
  check "same tag" ((int 5).tag = (int 5).tag);
  check "different tags"
    ((int 5).tag <> (int 6).tag
    && (node (Op2 (Plus, x, int 1)) TInt).tag
       <> (node (Op2 (Plus, int 1, x)) TInt).tag);
  check "same term"
    ((node (Op2 (Plus, x, int 1)) TInt).tag
    = (node (Op2 (Plus, x, int 1)) TInt).tag);
  check "fold" (plus (int 1) (int 2) == int 3);
  check "unit" (plus x (int 0) == x && plus (int 0) x == x);
  check "zero" (times x (int 0) == int 0 && times (int 1) x == x);
  check "fold to a bool" (lt_ (int 1) (int 2) == Tiny_prims.v_true);
  check "non-linear" (and_ p (not_ p) == Tiny_prims.v_false);
  check "same" (eq x x == Tiny_prims.v_true);
  check "commutative" (plus x (int 1) == plus (int 1) x);
  check "tests" (List.length Tiny_tests.rule_fns > 0);
  check "sorts of parameters"
    (is_zero (int 0) && (not (is_zero (int 1))) && zero == int 0);
  check "re-exported types"
    (equal_checked
       { signed = true; unsigned = false }
       { Tiny_base.signed = true; unsigned = false }
    && equal_rounding Nearest Tiny_base.Nearest);
  check "asserted sorts"
    (match is_zero p with _ -> false | exception Assert_failure _ -> true)

let () =
  let open Bool_lang in
  let v x = node (Var x) TBool in
  let a = v "a" and b = v "b" in
  check "and" (b_and a (b_not a) == Prims.v_false);
  check "or" (b_or a Prims.v_true == Prims.v_true);
  check "eq" (sem_eq a a == Prims.v_true);
  check "ite" (b_ite Prims.v_true a b == a);
  check "distinct" (b_distinct [ a; a ] == Prims.v_false)

let () =
  let open Hyg_types in
  let open Hyg_rules in
  let int n = node (Int (Z.of_int n)) TInt in
  let v = function Int z -> Z.to_int z | _ -> failwith "not a literal" in
  let value (t : t) = v t.kind in
  (* i = 1, j = 2, i1 = 3, i2 = 4, b, z = 5, on the literals 6 and 7 *)
  check "fold with parameters named like its literals"
    (value
       (mix (Z.of_int 1) (Z.of_int 2) (Z.of_int 3) (Z.of_int 4) true
          (Z.of_int 5) (int 6) (int 7))
    = 1 + 20 + 300 + 4000 + 50000 + 600000 + 7000000);
  check "fold of a unary operator, parameter named i"
    (value (neg (Z.of_int 3) (int 7)) = 21)

let () =
  let open Arrays_lang in
  let int n = node (Int (Z.of_int n)) TInt in
  let vec l = node (Vec (Iarray.of_list (List.map Z.of_int l))) TVec in
  let elems (t : t) =
    match t.kind with Vec a -> List.map Z.to_int (Iarray.to_list a) | _ -> []
  in
  let v = vec [ 10; 20; 30 ] in
  check "length" (len v == int 3 && len (vec []) == int 0);
  check "get" (get v (int 1) == int 20);
  check "set" (elems (set v (int 1) (int 5)) = [ 10; 5; 30 ]);
  check "set copies" (elems v = [ 10; 20; 30 ]);
  check "set, then get" (get (set v (int 2) (int 7)) (int 2) == int 7);
  check "hash-consing of arrays"
    (vec [ 1; 2 ] == vec [ 1; 2 ] && vec [ 1; 2 ] != vec [ 2; 1 ]);
  check "structural equality"
    (same_vec (Iarray.of_list [ Z.one ]) (Iarray.of_list [ Z.one ])
    && not (same_vec (Iarray.of_list [ Z.one ]) (Iarray.of_list [ Z.of_int 2 ]))
    );
  check "lists" (elems (vec_of_list [ Z.of_int 4; Z.of_int 5 ]) = [ 4; 5 ]);
  check "list round trip"
    (elements (vec_of_list [ Z.one; Z.of_int 2 ]) = [ Z.one; Z.of_int 2 ]);
  check "out of bounds is not simplified"
    (get v (int 3) == node (Op2 (Get, v, int 3)) TInt
    && set v (int (-1)) (int 0) == node (Op3 (Set, v, int (-1), int 0)) TVec)
