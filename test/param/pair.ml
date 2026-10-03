(* A host type with two parameters: the functions take the equality (or the
   hash) of each, in order. *)

type ('a, 'b) t = 'a * 'b

let equal ea eb (a1, b1) (a2, b2) = ea a1 a2 && eb b1 b2
let hash ha hb (a, b) = (ha a * 31) + hb b
