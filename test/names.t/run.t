A rule whose spec annotates the sort of an operand lists its rules in
`ocaml-tests`, like one without the annotation. The generated test binds the
variables of the sorts, and an operand of another sort fails its assertion.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > use "rules"
  > sort TBv of nat [@get Rules.size]
  > node Bv of int * nat (v, n) : TBv n
  > node Neg : TBv n -> TBv n
  > node Ext of nat * nat (from', to') : TBv n -> TBv (to' - from' + 1) when 0 <= from' && from' <= to' && to' < n
  > KN
  $ cat > rules.kn <<'KN'
  > prim size_of_ty : ty -> int
  > fn size (v : t) : int [@ty_only] = size_of_ty (type_of v)
  > fn clamp (n m : nat) : nat = if n < m then n else m
  > rule bv_ext : Ext (from', to', (v' : TBv sz')) =
  >   | full: _ when from' = 0 && to' = sz' - 1 -> v'
  >   | neg: Neg x' -> bv_ext from' to' x'
  > KN
  $ kanon ocaml-tests lang.knl | sed -n '/^let rule_fns/,$p'
  let rule_fns : (string * string list * (source -> test)) list = [
    ( "Rules.bv_ext",
      [ "full"; "neg"; "default" ],
      fun src ->
      let from' = (src.int ()) in
      let to' = (src.int ()) in
      let v' = (src.term ()) in
      {
        spec = (fun () -> (node (Op1 ((Ext ((Z.to_int from'), (Z.to_int to'))), v')) (TBv ((Z.to_int (Z.add (Z.sub to' from') Z.one))))));
        call = (fun () -> rules_bv_ext from' to' v');
        fired = (fun () -> (let sz' = (rules_size v') in
                           (assert (match v'.ty with
                                   | (TBv (kanon__n))
                                     when (let kanon__n = Z.of_int kanon__n in
                                     ((Z.leq Z.zero from') && ((Z.leq from' to') && (Z.lt to' kanon__n)))) ->
                                     true
                                   | _ -> false
                                   );
                           (match v' with
                           | _
                             when ((((Z.equal from' Z.zero)) && ((Z.equal to' (Z.sub sz' Z.one))))) ->
                             "full"
                           | { kind = Op1 ((Neg), x'); _ } -> "neg"
                           | _ -> "default"
                           ))));
      });
    ]
  
  let untested = [  ]
  

`nat` is a type of signatures, the same as `int`: a `Z.t` in OCaml, an `Int` in
Lean.

  $ kanon ocaml lang.knl | grep -A1 "clamp"
  let[@inline] rules_clamp (n : Z.t) (m : Z.t) : Z.t =
      (if (Z.lt n m) then n else m)
  $ kanon lean-model lang.knl | grep -A1 "def Rules.clamp"
  def Rules.clamp (n : Int) (m : Int) : Int :=
    (if (decide (n < m)) then n else m)

Identifiers may have primes, and a user type may still be called `nat`.

  $ kanon lean-model lang.knl | grep "def Rules.bv_ext.r_neg" -A3
  def Rules.bv_ext.r_neg (O : Ops) (from' : Int) (to' : Int) (v' : Term) : Option Term :=
    let sz' := (Rules.size v');
    (match v' with
      | (Term.mk (Kind.Op1 Op1.Neg x') _) =>
  $ cat > lang2.knl <<'KN'
  > use "rules2"
  > type nat [@ocaml "int"] [@lean "Nat"]
  > KN
  $ cat > rules2.kn <<'KN'
  > fn succ (n : nat) : nat = n
  > KN
  $ kanon ocaml lang2.knl | grep "succ"
  let[@inline] rules2_succ (n : nat) : nat = n
