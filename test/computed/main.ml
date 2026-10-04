open Cs_types
open Cs_rules

let check name b = if not b then failwith ("test failed: " ^ name)

let () =
  let one = node (Int Z.one) TInt in
  let tup = Rules.mk_tuple [ one; Rules.mk_tuple [ one ] ] in
  check "tuple sort" (tup.ty = TTuple [ TInt; TTuple [ TInt ] ]);
  check "field sort" ((Rules.mk_field Z.one tup).ty = TTuple [ TInt ]);
  check "field sort of a leaf" ((Rules.mk_field Z.zero tup).ty = TInt);
  check "field in" ((Rules.mk_field_in Z.zero tup).ty = tup.ty);
  check "var sort" ((Rules.mk_var "x" (TTuple [])).ty = TTuple []);
  check "var sort from a primitive" ((Rules.mk_var_of "b").ty = TTuple [ TInt ]);
  check "proj sort" ((Rules.proj Z.one tup).ty = TTuple [ TInt ])
