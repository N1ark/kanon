(* A host container: an immutable array, with the equality and the hash that
   take those of the elements. *)

type 'a t = 'a array

let equal eq a b =
  Array.length a = Array.length b
  &&
  let rec go i = i >= Array.length a || (eq a.(i) b.(i) && go (i + 1)) in
  go 0

let hash h a = Array.fold_left (fun acc x -> (acc * 31) + h x) 17 a
