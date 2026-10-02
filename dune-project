(lang dune 3.23)

(cram enable)

(using menhir 3.0)

(generate_opam_files)

(name kanon)

(version 0.1.0)

(source
 (github N1ark/kanon))

(package
 (name kanon)

(version 0.1.0)
 (synopsis "A rule language for verified smart constructors")
 (description
  "Kanon compiles the simplification rules of a value language to OCaml smart constructors, and to a Lean model of them with one soundness statement per rule.")
 (depends
  (ocaml
   (>= 5.5.0))
  (dune
   (>= 3.23))
  (menhir
   (>= 20230415))
  (ppxlib
   (>= 0.38.0))
  fmt
  (zarith
   (>= 1.13))
  (yojson
   (>= 2.0))
  (ocamlformat
   (and
    :with-dev-setup
    (= 0.29.0)))))
