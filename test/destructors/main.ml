open Ds_types
open Ds_rules

let check name b = if not b then failwith ("test failed: " ^ name)

let () =
  let z = Z.of_int in
  let a = node (Lit (z 1, 8)) (TBv 8) and b = node (Lit (z 2, 8)) (TBv 8) in
  let flag = node (Flag true) TBool in
  (* a leaf: its parameters *)
  check "as leaf" (as_lit a = Some (z 1, 8));
  check "is leaf" (is_lit a && (not (is_lit flag)) && is_flag flag);
  check "as other leaf" (as_lit flag = None && as_flag flag = Some true);
  (* an operator: its parameters, then its operands *)
  let sum = rules_add true a b in
  check "as operator" (as_add sum = Some (true, a, b));
  check "is operator" (is_add sum && not (is_add a));
  check "not an operator" (as_add a = None && as_not sum = None);
  check "unary"
    (as_not (rules_not_ flag) = Some flag && is_not (rules_not_ flag));
  (* an n-ary operator: the list *)
  check "n-ary" (as_concat (rules_concat [ a; b ]) = Some [ a; b ]);
  check "n-ary empty"
    (as_concat (rules_concat []) = Some [] && not (is_concat a));
  (* a sort: its arguments *)
  check "as sort" (as_tbv a.ty = Some 8 && as_tbv flag.ty = None);
  check "is sort" (is_tbv a.ty && is_tbool flag.ty && not (is_tbool a.ty));
  check "sort without arguments" (as_tbool flag.ty = Some ());
  check "sort with two arguments"
    (let t = TPair (TBv 8, TBool) in
     as_tpair t = Some (TBv 8, TBool) && is_tpair t && not (is_tpair a.ty))
