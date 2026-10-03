(* The primitives of rules.kn. *)

open Pa_types

let box_of_list = Array.of_list
let box_to_list = Array.to_list
let box_get b i = b.(Z.to_int i)
let ints_of_list = Array.of_list
let pair_make a i = (a, i)
