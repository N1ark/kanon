(* The primitives of lang.knl. *)

open Cs_types

let var_ty (x : string) : ty = if x = "b" then TTuple [ TInt ] else TInt
