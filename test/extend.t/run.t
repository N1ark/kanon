The final catch-all case of a function: `_`, or a tuple of blanks (`_, _`,
`_, _, _`, `(_, _), _`), which is strictly equivalent. The cases of `extend fn`
and `extend rule` go before it, and a rule function that ends with one has no
`default`. `x, _` and `_ as x` are not blanks.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > sort TInt
  > node Int of int : TInt
  > node Add : TInt -> TInt -> TInt
  > notation Int
  > infix "+" = Add, Base.add
  > KN

A helper over three scrutinees ends with `_`, `_, _, _` or `(_, _), _`, and over
a pair of pairs. The added case is in the OCaml and in the Lean model, before
the last case; Lean needs the helper to be `[@extensible]`, as each language
puts its cases together.

  $ cat > ext.kn <<'KN'
  > extend fn Base.f =
  >   | 3, _, _ -> 7
  > KN

  $ for last in '_ -> 0' '_, _, _ -> 0'; do
  >   cat > base.kn <<KN
  > fn f (a b : int) (c : bool) : int [@extensible] =
  >   match a, b, c with
  >   | 1, 2, true -> 5
  >   | $last
  > KN
  >   echo "=== $last"
  >   kanon ocaml lang.knl base.kn ext.kn | grep -n 'Z.of_int (\(5\|7\))\|Z.zero'
  >   kanon lean-model lang.knl base.kn ext.kn | grep -n 'some ((\(5\|7\) : Int))'
  > done
  === _ -> 0
  11:        (Z.of_int (5))
  14:        (Z.of_int (7))
  15:      | _ -> Z.zero
  62:    then some ((5 : Int))
  108:    (if (decide (kanon__1 = (3 : Int))) then some ((7 : Int)) else none))
  === _, _, _ -> 0
  11:        (Z.of_int (5))
  14:        (Z.of_int (7))
  15:      | (_, _, _) -> Z.zero
  62:    then some ((5 : Int))
  108:    (if (decide (kanon__1 = (3 : Int))) then some ((7 : Int)) else none))

  $ cat > ext.kn <<'KN'
  > extend fn Base.g =
  >   | (3, _), _ -> 7
  > KN

  $ for last in '_ -> 0' '(_, _), _ -> 0' '_, _ -> 0'; do
  >   cat > base.kn <<KN
  > fn g (a b : int) (c : bool) : int [@extensible] =
  >   match (a, b), c with
  >   | (1, 2), true -> 5
  >   | $last
  > KN
  >   echo "=== $last"
  >   kanon ocaml lang.knl base.kn ext.kn | grep -n 'Z.of_int (\(5\|7\))\|Z.zero'
  >   kanon lean-model lang.knl base.kn ext.kn | grep -n 'some ((\(5\|7\) : Int))'
  > done
  === _ -> 0
  11:        (Z.of_int (5))
  14:        (Z.of_int (7))
  15:      | _ -> Z.zero
  62:    then some ((5 : Int))
  108:    (if (decide (kanon__1 = (3 : Int))) then some ((7 : Int)) else none))
  === (_, _), _ -> 0
  11:        (Z.of_int (5))
  14:        (Z.of_int (7))
  15:      | ((_, _), _) -> Z.zero
  62:    then some ((5 : Int))
  108:    (if (decide (kanon__1 = (3 : Int))) then some ((7 : Int)) else none))
  === _, _ -> 0
  11:        (Z.of_int (5))
  14:        (Z.of_int (7))
  15:      | (_, _) -> Z.zero
  62:    then some ((5 : Int))
  108:    (if (decide (kanon__1 = (3 : Int))) then some ((7 : Int)) else none))

`x, _` and `_ as x` are not blanks: the added case is last, so it cannot be
reached, which is an error, not a silent omission.

  $ cat > ext.kn <<'KN'
  > extend fn Base.f =
  >   | 3, _, _ -> 7
  > KN

  $ for last in 'x, _, _ -> 0' '(_ as x), _, _ -> 0'; do
  >   cat > base.kn <<KN
  > fn f (a b : int) (c : bool) : int =
  >   match a, b, c with
  >   | 1, 2, true -> 5
  >   | $last
  > KN
  >   echo "=== $last"
  >   kanon ocaml lang.knl base.kn ext.kn
  >   kanon lean-model lang.knl base.kn ext.kn
  > done
  === x, _, _ -> 0
  ext.kn:2:4: extend Base.f: this case is unreachable (an earlier case of Base.f matches everything it does), so it was not added
  ext.kn:2:4: extend Base.f: this case is unreachable (an earlier case of Base.f matches everything it does), so it was not added
  === (_ as x), _, _ -> 0
  ext.kn:2:4: extend Base.f: this case is unreachable (an earlier case of Base.f matches everything it does), so it was not added
  ext.kn:2:4: extend Base.f: this case is unreachable (an earlier case of Base.f matches everything it does), so it was not added
  [1]

Likewise for a rule function: the cases added by `extend rule` go before a last
rule `_` or `_, _` (which is then the final catch-all: there is no `default`).
Without one, they are before `default`.

  $ cat > ext.kn <<'KN'
  > extend rule Base.add =
  >   | one: 1, x -> x
  > KN

  $ for last in '| fin: _ -> v1' '| fin: _, _ -> v1' ''; do
  >   cat > base.kn <<KN
  > rule add : Add (v1, v2) =
  >   | zero: 0, x -> x
  >   $last
  > KN
  >   echo "=== $last"
  >   kanon lean-rules lang.knl base.kn ext.kn | grep -A1 'firstSome \['
  >   kanon ocaml lang.knl base.kn ext.kn | grep -c 'Z.one'
  > done
  === | fin: _ -> v1
    (firstSome [Kanon.Base.Base.add.r_zero (S := sem) O.toBaseOps v1 v2, Kanon.Ext.Base.add.r_one (S := sem) O v1 v2, Kanon.Base.Base.add.r_fin (S := sem) O.toBaseOps v1 v2]).getD
      (Kanon.Base.Base.add.spec (S := sem) v1 v2)
  1
  === | fin: _, _ -> v1
    (firstSome [Kanon.Base.Base.add.r_zero (S := sem) O.toBaseOps v1 v2, Kanon.Ext.Base.add.r_one (S := sem) O v1 v2, Kanon.Base.Base.add.r_fin (S := sem) O.toBaseOps v1 v2]).getD
      (Kanon.Base.Base.add.spec (S := sem) v1 v2)
  1
  === 
    (firstSome [Kanon.Base.Base.add.r_zero (S := sem) O.toBaseOps v1 v2, Kanon.Ext.Base.add.r_one (S := sem) O v1 v2, Kanon.Base.Base.add.r_default (S := sem) O.toBaseOps v1 v2]).getD
      (Kanon.Base.Base.add.spec (S := sem) v1 v2)
  1

`extend rule Base.f before r` and a rule that is not a catch-all, `x, _`: the
added rule cannot be reached, which is an error.

  $ cat > base.kn <<'KN'
  > rule add : Add (v1, v2) =
  >   | zero: 0, x -> x
  >   | fin: x, _ -> v1
  > KN
  $ kanon ocaml lang.knl base.kn ext.kn
  ext.kn:2:9: extend Base.add: this case is unreachable (an earlier case of Base.add matches everything it does), so it was not added
  [1]

A case written after `_, _` is unreachable exactly as after `_`: it is left out.

  $ cat > base.kn <<'KN'
  > fn g (a b : int) : int =
  >   match a, b with
  >   | 1, _ -> 5
  >   | _, _ -> 0
  >   | 2, _ -> 6
  > fn h (a b : int) : int =
  >   match a, b with
  >   | 1, _ -> 5
  >   | _ -> 0
  >   | 2, _ -> 6
  > KN
  $ kanon ocaml lang.knl base.kn | grep -c "Z.of_int (6)"
  0
  [1]
  $ kanon lean-model lang.knl base.kn | grep -c "(6 : Int)"
  0
  [1]

An added case that is left out for any other reason (here, an earlier case
without a guard matches all that it matches) is an error, also for a rule.

  $ cat > base.kn <<'KN'
  > fn g (a b : int) : int =
  >   match a, b with
  >   | x, _ -> 5
  >   | _, _ -> 0
  > KN
  $ cat > ext.kn <<'KN'
  > extend fn Base.g =
  >   | 3, _ -> 7
  > KN
  $ kanon ocaml lang.knl base.kn ext.kn
  ext.kn:2:4: extend Base.g: this case is unreachable (an earlier case of Base.g matches everything it does), so it was not added
  [1]

A case of an extensible helper may call rule functions, oracles and extensible
helpers, itself included: it then takes the record `O` of the model. Each
language puts the cases together at each step of fuel, over the record of the
step before, and its default case at the first.

  $ cat > base.kn <<'KN'
  > fn h (a : t) : int [@extensible] =
  >   match a with
  >   | Int z -> z
  >   | _ -> 0
  > KN
  $ cat > ext.kn <<'KN'
  > extend fn Base.h =
  >   | x + _ -> Base.h x
  > KN
  $ kanon lean-model lang.knl base.kn ext.kn | grep '^def Base.h.c1'
  def Base.h.c1 (a : S.Term) : Option Int :=
  def Base.h.c1 (O : Ops S) (a : S.Term) : Option Int :=
  $ kanon lean-rules lang.knl base.kn ext.kn | grep -A1 '^def Base.h\|base_h :='
  def Base.h (O : Kanon.Ext.Ops sem) (a : Term) : Int :=
    (firstSome [Kanon.Base.Base.h.c1 (S := sem) a, Kanon.Ext.Base.h.c1 (S := sem) O a]).getD (Kanon.Base.Base.h.default (S := sem) a)
  --
      base_h := fun a => Kanon.Base.Base.h.default (S := sem) a }
  
  --
      base_h := Base.h O }
  
  --
      { base_h := fun a => Kanon.Base.Base.h.default.ok (S := sem) a }
    | n + 1 =>
  --
      { base_h := Base.h.sound _ hO }
  
