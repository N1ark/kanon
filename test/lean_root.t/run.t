Two modules with the same Lean root would write the same files, one over the
other: kanon lean-all reports it, and writes nothing.

  $ cat > lang.knl <<'KN'
  > use "a"
  > use "b"
  > KN
  $ cat > a.knl <<'KN'
  > [@@@lean_root "Same"]
  > sort TA
  > node A of int : TA
  > KN
  $ cat > b.knl <<'KN'
  > [@@@lean_root "Same"]
  > sort TB
  > node B of int : TB
  > KN
  $ kanon lean-all out lang.knl
  kanon: two modules write the Lean file Same/Node.lean: give them different roots with [@@@lean_root]
  [1]
  $ test -e out || echo nothing written
  nothing written
