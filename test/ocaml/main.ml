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
  check "fold" (Rules.plus (int 1) (int 2) == int 3);
  check "unit" (Rules.plus x (int 0) == x && Rules.plus (int 0) x == x);
  check "zero" (Rules.times x (int 0) == int 0 && Rules.times (int 1) x == x);
  check "fold to a bool" (Rules.lt_ (int 1) (int 2) == Tiny_prims.v_true);
  check "non-linear" (Rules.and_ p (Rules.not_ p) == Tiny_prims.v_false);
  check "same" (Rules.eq x x == Tiny_prims.v_true);
  check "commutative" (Rules.plus x (int 1) == Rules.plus (int 1) x);
  check "tests" (List.length Tiny_tests.rule_fns > 0);
  check "sorts of parameters"
    (Rules.is_zero (int 0)
    && (not (Rules.is_zero (int 1)))
    && Rules.zero == int 0);
  check "re-exported types"
    (equal_checked
       { signed = true; unsigned = false }
       { Tiny_base.signed = true; unsigned = false }
    && equal_rounding Nearest Tiny_base.Nearest);
  check "asserted sorts"
    (match Rules.is_zero p with
    | _ -> false
    | exception Assert_failure _ -> true)

let () =
  let open Bool_lang in
  let v x = node (Var x) TBool in
  let a = v "a" and b = v "b" in
  check "and" (Bool.and_ a (Bool.not_ a) == Prims.v_false);
  check "or" (Bool.or_ a Prims.v_true == Prims.v_true);
  check "eq" (Bool.eq a a == Prims.v_true);
  check "ite" (Bool.ite Prims.v_true a b == a);
  check "distinct" (Bool.distinct [ a; a ] == Prims.v_false)

let () =
  let open Hyg_types in
  let open Hyg_rules in
  let int n = node (Int (Z.of_int n)) TInt in
  let v = function Int z -> Z.to_int z | _ -> failwith "not a literal" in
  let value (t : t) = v t.kind in
  (* i = 1, j = 2, i1 = 3, i2 = 4, b, z = 5, on the literals 6 and 7 *)
  check "fold with parameters named like its literals"
    (value
       (Rules.mix (Z.of_int 1) (Z.of_int 2) (Z.of_int 3) (Z.of_int 4) true
          (Z.of_int 5) (int 6) (int 7))
    = 1 + 20 + 300 + 4000 + 50000 + 600000 + 7000000);
  check "fold of a unary operator, parameter named i"
    (value (Rules.neg (Z.of_int 3) (int 7)) = 21)

let () =
  let open Arrays_lang in
  let int n = node (Int (Z.of_int n)) TInt in
  let vec l = node (Vec (Iarray.of_list (List.map Z.of_int l))) TVec in
  let elems (t : t) =
    match t.kind with Vec a -> List.map Z.to_int (Iarray.to_list a) | _ -> []
  in
  let v = vec [ 10; 20; 30 ] in
  check "length" (Vec.len v == int 3 && Vec.len (vec []) == int 0);
  check "get" (Vec.get v (int 1) == int 20);
  check "set" (elems (Vec.set v (int 1) (int 5)) = [ 10; 5; 30 ]);
  check "set copies" (elems v = [ 10; 20; 30 ]);
  check "set, then get" (Vec.get (Vec.set v (int 2) (int 7)) (int 2) == int 7);
  check "hash-consing of arrays"
    (vec [ 1; 2 ] == vec [ 1; 2 ] && vec [ 1; 2 ] != vec [ 2; 1 ]);
  check "structural equality"
    (Vec.same (Iarray.of_list [ Z.one ]) (Iarray.of_list [ Z.one ])
    && not (Vec.same (Iarray.of_list [ Z.one ]) (Iarray.of_list [ Z.of_int 2 ]))
    );
  check "lists" (elems (Vec.of_list [ Z.of_int 4; Z.of_int 5 ]) = [ 4; 5 ]);
  check "list round trip"
    (Vec.elements (Vec.of_list [ Z.one; Z.of_int 2 ]) = [ Z.one; Z.of_int 2 ]);
  check "out of bounds is not simplified"
    (Vec.get v (int 3) == node (Op2 (Get, v, int 3)) TInt
    && Vec.set v (int (-1)) (int 0) == node (Op3 (Set, v, int (-1), int 0)) TVec
    )

let () =
  let open Trav_lang in
  let int n = node (Int (Z.of_int n)) TInt in
  let var x = node (Var x) TInt in
  let zero = int 0 and one = int 1 and two = int 2 in
  let add a b = Term.add a b in
  (* the children, in the order of the arguments *)
  let children v =
    let l = ref [] in
    iter_children (fun c -> l := c :: !l) v;
    List.rev !l
  in
  let tuple = node (Tuple [ one; two; zero ]) (TTuple [ TInt; TInt; TInt ]) in
  let vec = node (Vec (Iarray.of_list [ two; one ])) TVec in
  let opt = node (Opt (Some (Z.of_int 7, two))) TInt in
  let none = node (Opt None) TInt in
  let mem = node (Mem { owner = "p"; offset = one; size = two }) TBlock in
  let sum = node (Op2 (Add, one, two)) TInt in
  check "children of a leaf" (children (var "x") = [] && children one = []);
  check "children of an operator" (children sum = [ one; two ]);
  check "children of a list" (children tuple = [ one; two; zero ]);
  check "children of an array" (children vec = [ two; one ]);
  check "children of an option of a tuple"
    (children opt = [ two ] && children none = []);
  check "children of a record, in the order of its fields"
    (children mem = [ one; two ]);
  (* map: each child once, from the left; a node with a smart constructor is
     rebuilt through it, so that a zero disappears *)
  let order = ref [] in
  ignore
    (map_children
       (fun c ->
         order := c :: !order;
         c)
       sum);
  check "map visits the children from the left" (List.rev !order = [ one; two ]);
  check "map is rebuilt by the smart constructor"
    (map_children (fun c -> if c == two then zero else c) sum == one);
  let negx = node (Op1 (Neg, node (Op1 (Neg, var "x")) TInt)) TInt in
  check "map through the smart constructor of the extension"
    (map_children (fun c -> c) negx == var "x");
  (* a node without a smart constructor is rebuilt raw, at the sort of its
     typing: the sort of a tuple follows its elements *)
  let empty = node (Vec (Iarray.of_list [])) TVec in
  let mapped = map_children (fun _ -> empty) tuple in
  check "the sort of a tuple is computed from the new children"
    (mapped.ty = TTuple [ TVec; TVec; TVec ]
    && mapped.kind = Tuple [ empty; empty; empty ]);
  check "map of an array"
    ((map_children (fun _ -> one) vec).kind = Vec (Iarray.of_list [ one; one ]));
  check "map of an option of a tuple"
    ((map_children (fun _ -> one) opt).kind = Opt (Some (Z.of_int 7, one))
    && map_children (fun _ -> one) none == none);
  check "map of a record"
    ((map_children (fun _ -> two) mem).kind
    = Mem { owner = "p"; offset = two; size = two });
  check "a leaf is its own map"
    (map_children (fun _ -> zero) (var "x") == var "x");
  (* exists / for_all: short-circuit, in order *)
  let seen = ref [] in
  let p c =
    seen := c :: !seen;
    c == one
  in
  check "exists" (exists_child p tuple && List.rev !seen = [ one ]);
  seen := [];
  check "for_all stops at the first failure"
    ((not
        (for_all_child
           (fun c ->
             seen := c :: !seen;
             c == one)
           tuple))
    && List.rev !seen = [ one; two ]);
  check "for_all of a leaf, exists of a leaf"
    (for_all_child (fun _ -> false) one
    && not (exists_child (fun _ -> true) one));
  (* a recursive search without a handler or an allocation *)
  let rec has_var v =
    (match v.kind with Var _ -> true | _ -> false) || exists_child has_var v
  in
  check "recursive exists"
    (has_var (add (var "x") one)
    && (not (has_var (add one two)))
    && has_var (node (Mem { owner = "p"; offset = var "y"; size = one }) TBlock)
    );
  (* a host exception stops a traversal: iter has no handler of its own *)
  let exception Stop in
  let count = ref 0 in
  let rec walk v =
    incr count;
    if v == two then raise Stop;
    iter_children walk v
  in
  check "a host exception stops iter"
    ((try
        walk (add (add one two) (add one one));
        false
      with Stop -> true)
    && !count = 4);
  (* the sorts *)
  let sort = TTuple [ TInt; TVec ] in
  let tys = ref [] in
  iter_ty_children (fun t -> tys := t :: !tys) sort;
  check "children of a sort"
    (List.rev !tys = [ TInt; TVec ] && exists_ty_child (( = ) TVec) sort);
  check "map of a sort"
    (map_ty_children (fun _ -> TBlock) sort = TTuple [ TBlock; TBlock ]
    && map_ty_children (fun _ -> TBlock) TInt = TInt
    && for_all_ty_child (( = ) TInt) TInt);
  (* the nodes of the extension have their cases *)
  let nv = Ext.neg (var "x") in
  check "an added node"
    (children nv = [ var "x" ]
    && map_children (fun _ -> zero) nv == Ext.neg zero)
