`[@no_lean]` on a `fn` or a `prim`: it is checked, and generated in OCaml, but
it does not exist in the Lean files.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > [@@@ocaml_rules "Rules"]
  > sort TInt
  > node Int of int : TInt
  > node Add : TInt -> TInt -> TInt
  > notation Int
  > infix "+" = Add, add
  > KN

  $ cat > rules.kn <<'KN'
  > prim p_lean : int -> int
  > prim p_hidden : int -> int [@no_lean]
  > fn lean_helper (x : int) : int = p_lean x
  > fn hidden_helper (x : int) : int [@no_lean] = p_hidden (lean_helper x) + size_hidden x
  > fn size_hidden (x : int) : int [@no_lean] =
  >   match x with
  >   | 0 -> 1
  >   | _ -> 2
  > rule add : Add (v1, v2) =
  >   | zero: 0, x -> x
  > KN

  $ kanon ocaml lang.knl rules.kn | grep "hidden"
    val p_hidden : Z.t -> Z.t
    let[@inline] rules_size_hidden (x : Z.t) : Z.t =
    let[@inline] rules_hidden_helper (x : Z.t) : Z.t =
        (Z.add (Prims.p_hidden (rules_lean_helper x)) (rules_size_hidden x))
    let hidden_helper = Kanon_flat.rules_hidden_helper
    let size_hidden = Kanon_flat.rules_size_hidden
  $ kanon ocaml-typed lang.knl rules.kn | grep -c "hidden"
  0
  [1]
  $ kanon ocaml-tests lang.knl rules.kn | grep -c "hidden"
  0
  [1]
  $ for b in node lang model statements soundness syntax semantics rules; do
  >   echo "$b: $(kanon lean-$b lang.knl rules.kn | grep -c "hidden")"
  > done
  node: 0
  lang: 0
  model: 0
  statements: 0
  soundness: 0
  syntax: 0
  semantics: 0
  rules: 0
  $ kanon lean-model lang.knl rules.kn | grep "p_lean\|lean_helper"
  def Rules.lean_helper (x : Int) : Int :=
    (Kanon.Rules.p_lean x)
  attribute [kanon_body] Rules.lean_helper

A `[@no_lean]` function may call anything. A function or a rule that Lean models
may not call one, or a `[@no_lean]` primitive, even through a derived rule or in
the typing of a node.

  $ cat > bad.kn <<'KN'
  > prim p_hidden : int -> int [@no_lean]
  > fn hidden_helper (x : int) : int [@no_lean] = x
  > fn caller (x : int) : int = hidden_helper x
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:3:28: fn Bad.caller calls Bad.hidden_helper, which is [@no_lean]
  [1]

  $ cat > bad.kn <<'KN'
  > prim p_hidden : int -> int [@no_lean]
  > fn caller (x : int) : int = p_hidden x
  > KN
  $ kanon lean-model lang.knl bad.kn
  bad.kn:2:28: fn Bad.caller calls Bad.p_hidden, which is [@no_lean]
  [1]

  $ cat > bad.kn <<'KN'
  > fn hidden_helper (x : int) : int [@no_lean] = x
  > rule add : Add (v1, v2) =
  >   | zero: 0, x when hidden_helper 1 = 1 -> x
  > KN
  $ kanon ocaml lang.knl bad.kn
  bad.kn:3:20: rule Bad.add calls Bad.hidden_helper, which is [@no_lean]
  [1]

  $ cat > bad.kn <<'KN'
  > fn ok (x : int) : int [@no_lean] = x
  > fn unfold (x : int) : int [@no_lean] = ok x
  > KN
  $ kanon ocaml lang.knl bad.kn | grep -c unfold
  2

  $ cat > bad.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > sort TInt
  > node Int of int : TInt
  > node Add : TInt -> TInt -> TInt [@fold add_z]
  > node Pos of int (n) : TInt -> TInt when ok n
  > notation Int
  > infix "+" = Add, add
  > KN
  $ cat > bad.kn <<'KN'
  > fn add_z (x y : int) : int [@no_lean] = x + y
  > fn ok (x : int) : bool [@no_lean] = x > 0
  > rule add : Add (v1, v2)
  > KN
  $ kanon ocaml bad.knl bad.kn
  bad.knl:4:32: rule Bad.add calls Bad.add_z, which is [@no_lean]
  [1]
  $ sed -i 's/ \[@fold add_z\]//' bad.knl
  $ kanon ocaml bad.knl bad.kn
  bad.knl:5:40: the typing of Pos calls Bad.ok, which is [@no_lean]
  [1]

`extend fn` on a `[@no_lean]` function adds cases to the same function, which
are not modelled either, and may call other `[@no_lean]` functions.

  $ cat > base.kn <<'KN'
  > fn hidden_helper (x : int) : int [@no_lean] =
  >   match x with
  >   | 0 -> 1
  >   | _ -> 2
  > KN
  $ cat > ext.kn <<'KN'
  > fn other (x : int) : int [@no_lean] = x
  > extend fn Base.hidden_helper =
  >   | 3 -> other 4
  > KN
  $ kanon ocaml lang.knl base.kn ext.kn | grep -c "other"
  3
  $ kanon lean-model lang.knl base.kn ext.kn | grep -c "other\|hidden"
  0
  [1]

Only `fn` and `prim` items can be `[@no_lean]`, and unknown attributes on
`fn`, `prim` and `rule` are errors.

  $ for item in 'rule add : Add (v1, v2) [@no_lean]' 'oracle o : int -> int [@no_lean]' 'sort TFoo [@no_lean]' 'node Foo : TInt [@no_lean]' 'type foo [@no_lean]' 'fn f (x : int) : int [@ocaml_only] = x' 'prim q : int [@whatever]' 'rule add : Add (v1, v2) [@whatever]' 'rule add : Add (v1, v2) [@ty_only]' 'fn f (v : t) : int [@ty_only] [@no_lean] = 3'; do
  >   echo "=== $item"
  >   case "$item" in
  >   rule*|fn*|prim*|oracle*) printf '%s\n' "$item" > bad.kn; cp lang.knl bad.knl;;
  >   *) { cat lang.knl; printf '%s\n' "$item"; } > bad.knl; echo > bad.kn;;
  >   esac
  >   kanon ocaml bad.knl bad.kn
  > done
  === rule add : Add (v1, v2) [@no_lean]
  bad.kn:1:26: a rule is proved in Lean and cannot be [@no_lean]: only fn and prim items can be
  === oracle o : int -> int [@no_lean]
  bad.kn:1:24: an oracle is a parameter of the Lean model and cannot be [@no_lean]: only fn and prim items can be
  === sort TFoo [@no_lean]
  bad.knl:8:12: a sort is part of the Lean model and cannot be [@no_lean]: only fn and prim items can be
  === node Foo : TInt [@no_lean]
  bad.knl:8:18: a node is part of the Lean model and cannot be [@no_lean]: only fn and prim items can be
  === type foo [@no_lean]
  bad.knl:8:11: a type is part of the Lean model and cannot be [@no_lean]: only fn and prim items can be
  === fn f (x : int) : int [@ocaml_only] = x
  bad.kn:1:23: unknown attribute [@ocaml_only]
  === prim q : int [@whatever]
  bad.kn:1:15: unknown attribute [@whatever]
  === rule add : Add (v1, v2) [@whatever]
  bad.kn:1:26: unknown attribute [@whatever]
  === rule add : Add (v1, v2) [@ty_only]
  bad.kn:1:26: unknown attribute [@ty_only]
  === fn f (v : t) : int [@ty_only] [@no_lean] = 3
  (* Generated by kanon from bad.kn. Do not edit. *)
  
  [@@@warning "-a+11"]
  
  (** The functions of the language, in one recursive group, by their flat name: the module in lowercase, an underscore, and the name. The modules below are their names. Not meant to be used. *)
  module Kanon_flat = struct
    let[@inline] bad_f (v : t) : Z.t = (Z.of_int (3))
  end
  
  (** The Kanon module bad. *)
  module Bad = struct
    let t_int : ty = TInt
    let f = Kanon_flat.bad_f
    
    let as_int (t : t) =
      match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
    
    let is_int (t : t) =
      match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
    
    let as_add (t : t) =
      match[@warning "-11"] t with { kind = Op2 (Add, x1, x2); _ } -> Some (x1, x2) | _ -> None
    
    let is_add (t : t) =
      match[@warning "-11"] t with { kind = Op2 (Add, _, _); _ } -> true | _ -> false
    
    let as_tint (t : ty) =
      match[@warning "-11"] t with TInt -> Some () | _ -> None
    
    let is_tint (t : ty) =
      match[@warning "-11"] t with TInt -> true | _ -> false
  end
  
  
