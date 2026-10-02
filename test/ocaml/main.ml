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
