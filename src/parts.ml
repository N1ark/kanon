(** The generated code by part, printed on a formatter: what the web runtime
    shows (see web/), as [kanon] no longer prints it. [run [BACKEND; FILE...]]
    prints the OCaml of the language and its rules, with the backends
    [ocaml-types], [ocaml], [ocaml-typed] and [ocaml-tests], or one part of the
    Lean files of its modules and of the language, with [lean-PART] for each
    part of {!Gen_lean.parts}, as [kanon ocaml] and [kanon lean] would write
    them, each file after its name when a part has several. *)

(** The backends, in order. *)
let backends =
  [ "ocaml-types"; "ocaml"; "ocaml-typed"; "ocaml-tests" ]
  @ List.map
      (fun (part, _) -> "lean-" ^ part)
      (Gen_lean.parts ~module_only:false ~lang:[]
         ~has_proof:(fun _ _ -> false)
         (lazy (assert false)))

let usage err =
  Format.fprintf err "usage: BACKEND FILE...@.The backends are %s.@."
    (String.concat ", " backends)

(** [run args out err] prints the part that [args] ask for on [out], and is the
    exit code, as {!Cli.run}. *)
let run args out err =
  Cli.guard ~usage err (fun () ->
      match args with
      | backend :: files -> (
          let { Cli.lang; sources; prog; module_only } = Cli.load err files in
          let ocaml print =
            if sources = [] then raise Cli.Usage;
            print (Lazy.force prog);
            0
          in
          match backend with
          | "ocaml-types" ->
              Gen_ocaml.types ~sources:lang out;
              0
          | "ocaml" -> ocaml (fun p -> Gen_ocaml.program ~sources out p)
          | "ocaml-typed" ->
              ocaml (fun p -> Gen_typed.program ~sources:(lang @ sources) out p)
          | "ocaml-tests" ->
              ocaml (fun p ->
                  Gen_tests.program ~open_module:(Cli.rules_module ()) ~sources
                    out p)
          | _ -> (
              let parts =
                Gen_lean.parts ~module_only ~lang
                  ~has_proof:(fun _ _ -> false)
                  prog
              in
              match
                List.assoc_opt backend
                  (List.map (fun (part, gen) -> ("lean-" ^ part, gen)) parts)
              with
              | Some gen ->
                  let files = gen () in
                  List.iteri
                    (fun i (f : Gen_lean.file) ->
                      if List.length files > 1 then
                        Format.fprintf out "%s-- %s@.@."
                          (if i > 0 then "\n" else "")
                          (Gen_lean.file_name f);
                      Format.fprintf out "%s@?" (Cli.contents f))
                    files;
                  0
              | None -> raise Cli.Usage))
      | [] -> raise Cli.Usage)
