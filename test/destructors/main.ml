open Ds_types
open Ds_rules

let check name b = if not b then failwith ("test failed: " ^ name)

let () =
  let z = Z.of_int in
  let a = node (Lit (z 1, 8)) (TBv 8) and b = node (Lit (z 2, 8)) (TBv 8) in
  let flag = node (Flag true) TBool in
  (* a leaf: its parameters *)
  check "as leaf" (Lang.as_lit a = Some (z 1, 8));
  check "is leaf"
    (Lang.is_lit a && (not (Lang.is_lit flag)) && Lang.is_flag flag);
  check "as other leaf"
    (Lang.as_lit flag = None && Lang.as_flag flag = Some true);
  (* an operator: its parameters, then its operands *)
  let sum = Rules.add true a b in
  check "as operator" (Lang.as_add sum = Some (true, a, b));
  check "is operator" (Lang.is_add sum && not (Lang.is_add a));
  check "not an operator" (Lang.as_add a = None && Lang.as_not sum = None);
  check "unary"
    (Lang.as_not (Rules.not_ flag) = Some flag && Lang.is_not (Rules.not_ flag));
  (* an n-ary operator: the list *)
  check "n-ary" (Lang.as_concat (Rules.concat [ a; b ]) = Some [ a; b ]);
  check "n-ary empty"
    (Lang.as_concat (Rules.concat []) = Some [] && not (Lang.is_concat a));
  (* a sort: its arguments *)
  check "as sort" (Lang.as_tbv a.ty = Some 8 && Lang.as_tbv flag.ty = None);
  check "is sort"
    (Lang.is_tbv a.ty && Lang.is_tbool flag.ty && not (Lang.is_tbool a.ty));
  check "sort without arguments" (Lang.as_tbool flag.ty = Some ());
  check "sort with two arguments"
    (let t = TPair (TBv 8, TBool) in
     Lang.as_tpair t = Some (TBv 8, TBool)
     && Lang.is_tpair t
     && not (Lang.is_tpair a.ty))
