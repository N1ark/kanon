A file that does not exist is an error of kanon, not an uncaught exception, for
every command, whether it is given on the command line or used by a module.

  $ kanon ocaml out nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon ocaml --check out nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon lean out nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]
  $ kanon lean --check out nofile.knl
  kanon: nofile.knl: No such file or directory
  [1]

  $ cat > lang.knl <<'KN'
  > use "m"
  > KN
  $ cat > m.knl <<'KN'
  > sort T
  > KN
  $ kanon ocaml out lang.knl nofile.kn
  kanon: nofile.kn: No such file or directory
  [1]
  $ cat > lang2.knl <<'KN'
  > use "x"
  > KN
  $ kanon ocaml out lang2.knl
  kanon: use "x": no ./x.knl or ./x.kn
  [1]

A file that cannot be read is named too:

  $ mkdir dir.knl
  $ kanon ocaml out dir.knl
  kanon: dir.knl: Is a directory
  [1]
