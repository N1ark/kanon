A `nat` argument of a sort is a width: the generated OCaml builds a sort only
with a strictly positive one, and raises `Invalid_argument` otherwise, in the
function of the sort (`t_bv`) and in the sort of a node. The `nat` of a node
that is not a sort (the index of `Field`) may be zero, and a pattern, which
builds nothing, does not check.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_types "T"]
  > [@@@traversals]
  > use "rules"
  > sort TBv of nat
  > sort TPair of nat * nat
  > sort TVec of ty * nat
  > node Bv of int * nat (v, n) : TBv n
  > node Ext of nat * nat (hi, lo) : TBv n -> TBv (hi - lo + 1)
  > node Field of nat (i) : TBv n -> TBv n
  > KN
  $ cat > rules.kn <<'KN'
  > fn mk_bv (v : int) (n : int) : t = Bv (v, n)
  > fn mk_pair (a : int) (b : int) : ty = TPair (a, b)
  > fn mk_vec (s : ty) (n : int) : ty = TVec (s, n)
  > rule ext : Ext (hi, lo, x) = | any : _ -> Ext (hi, lo, x)
  > rule field : Field (i, x) = | any : _ -> Field (i, x)
  > KN
  $ kanon ocaml-types lang.knl > t.ml
  $ kanon ocaml lang.knl > r.ml
  $ cat > main.ml <<'ML'
  > let attempt name f =
  >   match f () with
  >   | _ -> Printf.printf "%s: ok\n" name
  >   | exception Invalid_argument m ->
  >       Printf.printf "%s: Invalid_argument %S\n" name m
  > 
  > let () =
  >   let z = Z.of_int in
  >   let x = R.Rules.mk_bv (z 1) (z 8) in
  >   attempt "t_bv 8" (fun () -> R.Lang.t_bv 8);
  >   attempt "t_bv 0" (fun () -> R.Lang.t_bv 0);
  >   attempt "t_bv -3" (fun () -> R.Lang.t_bv (-3));
  >   attempt "t_pair 2 3" (fun () -> R.Lang.t_pair 2 3);
  >   attempt "t_pair 2 0" (fun () -> R.Lang.t_pair 2 0);
  >   attempt "t_vec" (fun () -> R.Lang.t_vec (R.Lang.t_bv 8) 0);
  >   attempt "sort in a rule" (fun () -> R.Rules.mk_pair (z 0) (z 2));
  >   attempt "node of width 8" (fun () -> R.Rules.mk_bv (z 1) (z 8));
  >   attempt "node of width 0" (fun () -> R.Rules.mk_bv (z 1) (z 0));
  >   attempt "extract 7 0" (fun () -> R.Rules.ext (z 7) (z 0) x);
  >   attempt "extract of width 0" (fun () -> R.Rules.ext (z 3) (z 4) x);
  >   attempt "index 0" (fun () -> R.Rules.field (z 0) x);
  >   (* a pattern does not check *)
  >   assert (R.Lang.as_tbv (T.TBv 0) = Some 0);
  >   (* a traversal keeps the width of a sort that it rebuilds *)
  >   (match R.map_ty_children (fun _ -> T.TBv 4) (T.TVec (T.TBv 8, 3)) with
  >   | T.TVec (T.TBv 4, 3) -> print_endline "map_ty_children: ok"
  >   | _ -> print_endline "map_ty_children: wrong")
  > ML
  $ ocamlfind ocamlopt -package zarith -linkpkg -w -a t.ml r.ml main.ml -o main.exe 2>&1 | head -5
  $ ./main.exe
  t_bv 8: ok
  t_bv 0: Invalid_argument "TBv: nat argument 1 must be positive, got 0"
  t_bv -3: Invalid_argument "TBv: nat argument 1 must be positive, got -3"
  t_pair 2 3: ok
  t_pair 2 0: Invalid_argument "TPair: nat argument 2 must be positive, got 0"
  t_vec: Invalid_argument "TVec: nat argument 2 must be positive, got 0"
  sort in a rule: Invalid_argument "TPair: nat argument 1 must be positive, got 0"
  node of width 8: ok
  node of width 0: Invalid_argument "TBv: nat argument 1 must be positive, got 0"
  extract 7 0: ok
  extract of width 0: Invalid_argument "TBv: nat argument 1 must be positive, got 0"
  index 0: ok
  map_ty_children: ok
