open Pa_types
open Pa_rules

let check name b = if not b then failwith ("test failed: " ^ name)
let int n = node (Int (Z.of_int n)) TInt

let () =
  let a = int 1 and b = int 2 in
  (* equal boxes make the same term, different ones different terms *)
  check "same box, same term" (mk_arr [ a; b ] == mk_arr [ int 1; int 2 ]);
  check "different order" (mk_arr [ a; b ] != mk_arr [ b; a ]);
  check "different length" (mk_arr [ a ] != mk_arr [ a; b ]);
  check "empty" (mk_arr [] == mk_arr []);
  (* the elements are compared as terms, not structurally *)
  check "nested" (mk_arr [ mk_arr [ a ]; b ] == mk_arr [ mk_arr [ int 1 ]; b ]);
  check "nested differ" (mk_arr [ mk_arr [ a ] ] != mk_arr [ mk_arr [ b ] ]);
  (* the same container at another type: integers *)
  let z = Z.of_int in
  check "ints" (mk_ints [ z 1; z 2 ] == mk_ints [ z 1; z 2 ]);
  check "ints differ" (mk_ints [ z 1; z 2 ] != mk_ints [ z 1; z 3 ]);
  (* two parameters, and containers in options *)
  let bx = Pa_prims.box_of_list [ a ] in
  check "pairs" (mk_pairs a (z 1) (Some bx) == mk_pairs a (z 1) (Some bx));
  check "pairs differ (int)" (mk_pairs a (z 1) None != mk_pairs a (z 2) None);
  check "pairs differ (term)" (mk_pairs a (z 1) None != mk_pairs b (z 1) None);
  check "pairs differ (option)"
    (mk_pairs a (z 1) None != mk_pairs a (z 1) (Some bx));
  (* values flow through functions *)
  check "operands" (operands (mk_arr [ a; b ]) = [ a; b ]);
  check "operands of a leaf" (operands a = []);
  check "rebuild" (rebuild (mk_arr [ a ]) [ a; b ] == mk_arr [ a; b ]);
  check "nth" (nth (mk_arr [ a; b ]) (z 1) == b);
  let bs = boxes (mk_arr [ a; b ]) in
  check "boxes" (bs <> None);
  let bx2 = Option.get bs in
  check "same_box" (same_box bx2 (Pa_prims.box_of_list [ int 1; int 2 ]));
  check "same_box differs" (not (same_box bx2 (Pa_prims.box_of_list [ a ])));
  check "pair of boxes" (fst (box_pair bx2) == bx2 && snd (box_pair bx2) == bx2);
  check "list of boxes" (List.length (boxes_list bx2) = 2)
