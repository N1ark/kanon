The empty list, the empty array and `None` are written with their type in
Lean, which cannot infer it from a match on them, nor from `arrayLength`:

  $ cat > lang.knl <<'KN'
  > use "rules"
  > sort TInt
  > node Int of int : TInt
  > KN
  $ cat > rules.kn <<'KN'
  > fn f (x : int) : int =
  >   match ([] : int list) with
  >   | [] -> x
  >   | y :: _ -> y
  > fn g (x : int) : int =
  >   match (None : int option) with
  >   | None -> x
  >   | Some z -> z
  > fn k (x : int) : int = array_length ([||] : int array) + x
  > KN
  $ kanon lean-model lang.knl | sed -n "/def Rules.f /,/^attribute/p"
  def Rules.f (x : Int) : Int :=
    ((firstSome [(match ([] : (List Int)) with | [] => some (x) | _ => none),
      (match ([] : (List Int)) with | (y :: _) => some (y) | _ => none)]).getD
      Inhabited.default)
  
  def Rules.g (x : Int) : Int :=
    ((firstSome [(match (none : (Option Int)) with
                   | none =>
                   some (x)
                   | _ => none),
      (match (none : (Option Int)) with | (some z) => some (z) | _ => none)]).getD
      Inhabited.default)
  
  def Rules.k (x : Int) : Int :=
    ((arrayLength (#[] : (Array Int))) + x)
  
  attribute [kanon_body] Rules.f Rules.g Rules.k
