A function whose result is annotated with a sort, like its parameters can be
(`fn f (a b : TBv n) : TBv n`), is typed by `ocaml-typed`: its parameters have
the tags of their sorts, and its result the tag of its own. The generated OCaml
asserts the sort of the result on exit, as it does for the parameters on entry.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_rules "Rules"]
  > use "bv"
  > KN
  $ cat > bv.knl <<'KN'
  > sort TBv of nat
  > sort TBool
  > node BitVec of int * nat (v, n) : TBv n
  > node Add of bool : TBv n -> TBv n -> TBv n
  > node Ult : TBv n -> TBv n -> TBool
  > KN
  $ cat > bv.kn <<'KN'
  > rule add : Add (checked, v1, v2)
  > 
  > (** Addition that wraps. *)
  > fn wrapping_add (a b : TBv n) : TBv n = add false a b
  > 
  > fn less (a b : TBv n) (flip : bool) : TBool = if flip then Ult (b, a) else Ult (a, b)
  > 
  > fn plain (a : t) : t = a
  > KN
  $ kanon ocaml lang.knl | sed -n '/^  let bv_wrapping_add/,/^$/p'
    let bv_wrapping_add (a : t) (b : t) : t =
        (let n = (match a.ty with
                 | (TBv (n)) -> let n = Z.of_int n in n
                 | _ -> (assert false)
                 ) in
        (let n = (match b.ty with
                 | (TBv (n)) -> let n = Z.of_int n in n
                 | _ -> (assert false)
                 ) in
        (let kanon__result = (assert ((match a.ty, b.ty with
                                      | ((TBv (kanon__v_n)), (TBv (kanon__s1)))
                                        when (let kanon__v_n = Z.of_int kanon__v_n in
                                        let kanon__s1 = Z.of_int kanon__s1 in
                                        ((Z.equal kanon__s1 kanon__v_n))) ->
                                        true
                                      | _ -> false
                                      ) [@warning "-11"]);
                             (bv_add false a b)) in
        (assert (((equal_ty kanon__result.ty (TBv ((Z.to_int n))))) [@warning "-11"]);
        kanon__result))))
    
    let bv_less (a : t) (b : t) (flip : bool) : t =
        (let kanon__result = (assert ((match a.ty, b.ty with
                                      | ((TBv (kanon__v_n)), (TBv (kanon__s1)))
                                        when (let kanon__v_n = Z.of_int kanon__v_n in
                                        let kanon__s1 = Z.of_int kanon__s1 in
                                        ((Z.equal kanon__s1 kanon__v_n))) ->
                                        true
                                      | _ -> false
                                      ) [@warning "-11"]);
                             (if flip
                             then (node (Op2 (Ult, b, a)) TBool)
                             else (node (Op2 (Ult, a, b)) TBool))) in
        (assert (((equal_ty kanon__result.ty TBool)) [@warning "-11"]);
        kanon__result))
    
    let[@inline] bv_plain (a : t) : t = a
  end
  

The typed interface has it, in the module of its file, with the tags of the
sorts of its parameters, and its other parameters by their types; a function
whose result is not annotated is not in it:

  $ kanon ocaml-typed lang.knl | grep "val \(add\|wrapping_add\|less\|plain\)\|Kanon_rules.bv_\(wrapping\|less\)"
      val add : bool -> [< Tag.tbv ] t -> [< Tag.tbv ] t -> [> Tag.tbv ] t
      val wrapping_add : [< Tag.tbv ] t -> [< Tag.tbv ] t -> [> Tag.tbv ] t
      val less : [< Tag.tbv ] t -> [< Tag.tbv ] t -> bool -> [> Tag.tbool ] t

Lean does not model the annotation: the function is the same as without it.

  $ kanon lean-model lang.knl | grep -A2 "def Bv.wrapping_add"
  def Bv.wrapping_add (O : Ops S) (a : S.Term) (b : S.Term) : S.Term :=
    (let n := ((firstSome [(match (Kanon.Bv.sortProj (S.ty a)) with
                             | some (.TBv n) =>
  $ kanon lean-statements lang.knl | grep -c "wrapping"
  0
  [1]

Its result sort is a sort (not a subsort, nor a type), over the variables that
its parameters bind:

  $ cat > bad.kn <<'KN'
  > fn f (a b : TBv n) : TBv m = a
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:25: unbound variable m
  [1]
  $ cat > bad.kn <<'KN'
  > fn f (a : TBv n) : Nope = a
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:1:19: unknown constructor Nope
  [1]
