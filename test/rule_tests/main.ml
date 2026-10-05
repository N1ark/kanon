(* The generated differential tests of rules whose spec annotates the sort of an
   operand list their rules, and are run on random terms: the test of an operand
   of the wrong sort fails an assertion and is retried. *)

open Rt_types
open Rt_rules
open Rt_tests

let check name b = if not b then failwith ("test failed: " ^ name)

let src : source =
  let rec term () =
    let w = 1 + Random.int 4 in
    match Random.int 3 with
    | 0 -> node (Bv (Z.of_int (Random.int 4), w)) (TBv w)
    | _ ->
        let x = term () in
        node (Op1 (Neg, x)) x.ty
  in
  {
    int = (fun () -> Z.of_int (Random.int 4));
    bool = Random.bool;
    term;
    terms = (fun () -> List.init (Random.int 3) (fun _ -> term ()));
    choose = Random.int;
  }

let () =
  let names n = List.map (fun (m, rs, _) -> (m, rs)) rule_fns |> List.assoc n in
  check "annotated spec lists its rules"
    (names "Rules.ext" = [ "full"; "neg"; "default" ]);
  check "plain spec lists its rules"
    (names "Rules.ext_plain" = [ "full"; "neg"; "default" ]);
  List.iter
    (fun (name, rules, mk) ->
      let rec run tries =
        check (name ^ ": no valid operands") (tries < 10_000);
        match mk src with
        | exception Assert_failure _ -> run (tries + 1)
        | t -> (
            match (t.call (), t.fired ()) with
            | _, r -> check (name ^ ": " ^ r) (List.mem r rules)
            | exception Assert_failure _ -> run (tries + 1))
      in
      for _ = 1 to 200 do
        run 0
      done)
    rule_fns;
  check "nat" (Z.equal (Rules.clamp (Z.of_int 3) (Z.of_int 2)) (Z.of_int 2))
