open Sub_types

let size (t : t) = match t.ty with TBitVector n -> Z.of_int n | _ -> Z.zero

let one n =
  let n = Z.to_int n in
  node (BitVec (Z.one, n)) (TBitVector n)
