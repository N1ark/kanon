Names that Lean reads as keywords are quoted in the Lean files, in a position
where Lean reads the quotes: a name that follows a prefix is not quoted, as
`r_«at»` is the name `r_` and then `«at»`.

A rule named after a keyword has the rule function `r_at`, with the arms and
the soundness theorems of its name:

  $ cat > lang.knl <<'KN'
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Neg : TInt -> TInt
  > KN
  $ cat > rules.kn <<'KN'
  > rule neg : Neg v =
  >   | at: Neg x -> x
  > KN
  $ kanon lean-all out lang.knl
  $ grep -rhoE 'Rules\.neg\.r_[^ .]*' out | sort -u
  Rules.neg.r_at
  Rules.neg.r_default

The primed parameters of a lifting lemma (`from'`) are quoted as their name is,
not as a prefix of it (`«from»'` is a quoted name and a quote):

  $ cat > lang2.knl <<'KN'
  > use "rules2"
  > sort TInt
  > node Int of int : TInt
  > notation Int
  > node Add : TInt -> TInt -> TInt
  > KN
  $ cat > rules2.kn <<'KN'
  > rule add : Add (from, at) =
  >   | zero: x, 0 -> x
  > KN
  $ kanon lean-all out2 lang2.knl
  $ grep -h -A4 'theorem lift_' out2/Kanon/Rules2/Lift.lean
  theorem lift_rules2_add (hO : O.Sound) {«from» from' : S.Term} {«at» at' : S.Term}
    (h_from : S.Refines «from» from')
    (h_at : S.Refines «at» at') :
    S.Refines (Kanon.Rules2.Rules2.add.spec «from» «at») (O.rules2_add from' at') :=
    Kanon.Sem.Refines.trans (Kanon.Sem.Refines.of_WT fun kw => by
