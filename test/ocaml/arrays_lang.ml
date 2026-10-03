(* The example language of examples/arrays: its types, its primitives and its
   rules, in one module, which uses the standard immutable arrays. *)

[%%include_file "arrays_types.gen.ml"]

module Prims = struct
  let v_true = node (Bool true) TBool
  let v_false = node (Bool false) TBool

  let sort_by_tag l =
    List.sort_uniq (fun (a : t) (b : t) -> Int.compare a.tag b.tag) l
end

[%%include_file "arrays_rules.gen.ml"]
