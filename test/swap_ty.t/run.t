An arm derived by commutativity is proved from its main arm only when its body
does not read the type of a swapped term: the types are only propositionally
equal. Otherwise it is proved on its own.

  $ cat > lang.knl <<'KN'
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Plus : TInt -> TInt -> TInt [@comm]
  > node Neg : TInt -> TInt
  > KN
  $ cat > rules.kn <<'KN'
  > rule neg : Neg v =
  >   | r: Plus (x, 0) -> (Int 1 : type_of v)
  > KN
  $ kanon lean . lang.knl > /dev/null
  $ grep -A1 "swap.ok :" Generated/Kanon/Rules/Soundness/Rules/neg.lean
  theorem Rules.neg.r_r.swap.ok : Rules.neg.r_r.swap.Stmt :=
    no_implicit_lambda% (kanon_proof% Rules.neg.r_r.swap)
