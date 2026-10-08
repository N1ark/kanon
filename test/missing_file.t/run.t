A file that does not exist is an error of kanon, not an uncaught exception, for
every backend, whether it is given on the command line or used by a module.

  $ kanon ocaml nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon ocaml-types nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon ocaml-typed nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon ocaml-tests nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon lean-types nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon lean-all out nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon lean-all --check out nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]

  $ cat > lang.knl <<'KN'
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort T
  > KN
  $ kanon ocaml lang.knl nofile.kn
  kanon: nofile.kn: No such file or directory
  [1]
  $ cat > lang2.knl <<'KN'
  > use "x"
  > KN
  $ kanon ocaml lang2.knl
  kanon: use "x": no ./x.knl or ./x.kn
  [1]

A file that cannot be read is named too:

  $ mkdir dir.knl
  $ kanon ocaml dir.knl
  kanon: dir.knl: Is a directory
  [1]
