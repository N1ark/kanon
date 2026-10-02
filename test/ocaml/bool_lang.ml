(* The example language of examples/bool: its types, its primitives and its
   rules, in one module. *)

[%%include_file "bool_types.gen.ml"]

module Prims = struct
  let v_true = node (Bool true) TBool
  let v_false = node (Bool false) TBool

  let sort_by_tag l =
    List.sort_uniq (fun (a : t) (b : t) -> Int.compare a.tag b.tag) l
end

[%%include_file "bool_rules.gen.ml"]
