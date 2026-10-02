The language server, kanon lsp, reads messages framed with their length, and
writes them one per line here, with ROOT for this directory, and BUILTIN for
the directory where it writes the modules built into kanon.

  $ msg() {
  >   m=$(printf '%s' "$1" | sed "s|ROOT|$PWD|g")
  >   printf 'Content-Length: %d\r\n\r\n%s' "${#m}" "$m"
  > }
  $ lsp() {
  >   kanon lsp < input |
  >   sed -e 's/Content-Length: [0-9]*\r$//' -e '/^\r*$/d' -e "s|$PWD|ROOT|g" \
  >     -e 's|file://[^"]*/kanon-modules-[0-9a-f]*/|BUILTIN/|g'
  > }
  $ init='{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT","capabilities":{}}}'
  $ at() {
  >   printf '{"jsonrpc":"2.0","id":%s,"method":"textDocument/%s","params":{"textDocument":{"uri":"file://ROOT/%s"},"position":{"line":%s,"character":%s}}}' "$@"
  > }
  $ change() {
  >   printf '{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file://ROOT/%s","version":2},"contentChanges":[{"text":"%s"}]}}' "$@"
  > }
  $ open() {
  >   printf '{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://ROOT/%s","languageId":"kanon","version":1,"text":"%s"}}}' "$@"
  > }

The language lang.knl uses the bool module and the modules imp (imp.knl and
imp.kn) and more (more.kn): it is the root that the other files are checked
with. imp.kn, on disk, has a type error, reported on imp.kn when more.kn is
opened. Opening imp.kn with the error fixed clears it; a syntax error is
reported on the word where it is found, and a missing module on its use.
Requests are answered after the changes before them are checked.

  $ IMP='(* [neg a] is the negation of [a]. *)\nfn neg (a : t) : t = b_not a\n\nrule b_imp : Imp (v1, v2) =\n  | false_: false implies _ -> v_true\n  | true_: true implies x -> x\n  | not_: x implies false -> neg x\n'
  $ MORE='extend rule b_imp before true_ =\n  | same: x implies x -> v_true\n'
  $ {
  >   msg "$init"
  >   msg '{"jsonrpc":"2.0","method":"initialized","params":{}}'
  >   msg "$(open more.kn "$MORE")"
  >   msg "$(at 1 hover more.kn 0 26)"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 2 hover imp.kn 6 29)"
  >   msg "$(change imp.kn "$(printf '%s' "$IMP" | sed 's/b_not a/b_not a in/')")"
  >   msg "$(at 3 hover imp.kn 3 14)"
  >   msg "$(change imp.kn "$IMP")"
  >   msg "$(change more.kn "use \\\"missing\\\"\\n$MORE")"
  >   msg "$(at 4 definition more.kn 1 26)"
  >   msg "$(change more.kn "$MORE")"
  >   msg '{"jsonrpc":"2.0","id":5,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"renameProvider":{"prepareProvider":true},"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true,"workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true}}},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[{"range":{"start":{"line":1,"character":27},"end":{"line":1,"character":28}},"severity":1,"source":"kanon","message":"type mismatch: expected t, got int"}]}}
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nrule b_imp =\n  | true_: true implies x -> x\n```\n\n*imp.kn*"},"range":{"start":{"line":0,"character":25},"end":{"line":0,"character":30}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","id":2,"result":{"contents":{"kind":"markdown","value":"```kanon\nfn neg (a : t) : t\n```\n\n[neg a] is the negation of [a].\n\n*imp.kn*"},"range":{"start":{"line":6,"character":29},"end":{"line":6,"character":32}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[{"range":{"start":{"line":1,"character":29},"end":{"line":1,"character":31}},"severity":1,"source":"kanon","message":"syntax error"}]}}
  {"jsonrpc":"2.0","id":3,"result":{"contents":{"kind":"markdown","value":"```kanon\nnode Imp : TBool -> TBool -> TBool\n```\n\nImplication.\n\n*imp.knl*"},"range":{"start":{"line":3,"character":13},"end":{"line":3,"character":16}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/more.kn","diagnostics":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":13}},"severity":1,"source":"kanon","message":"use \"missing\": no ROOT/missing.knl or ROOT/missing.kn"}]}}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}}]}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/more.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","id":5,"result":null}

Navigation: the definitions of a function, a node, an operator, a rule after
before (in the function that extend extends), a function of the bool module,
built into kanon, which the server writes to a file, and of the type of terms
t. Hover shows the header of the definition (here of a sort), and the comment
before it.

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 1 definition imp.kn 6 29)"
  >   msg "$(at 2 definition imp.kn 3 14)"
  >   msg "$(at 3 definition imp.kn 4 20)"
  >   msg "$(at 4 definition more.kn 0 26)"
  >   msg "$(at 5 definition imp.kn 1 23)"
  >   msg "$(at 6 hover imp.kn 1 23)"
  >   msg "$(at 7 definition imp.kn 1 12)"
  >   msg "$(at 8 hover imp.knl 1 12)"
  >   msg '{"jsonrpc":"2.0","id":9,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v publishDiagnostics
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"renameProvider":{"prepareProvider":true},"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true,"workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true}}},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","id":1,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":1,"character":3},"end":{"line":1,"character":6}}}]}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":1,"character":5},"end":{"line":1,"character":8}}}]}
  {"jsonrpc":"2.0","id":3,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":14}}}]}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}}]}
  {"jsonrpc":"2.0","id":5,"result":[{"uri":"BUILTIN/bool.kn","range":{"start":{"line":50,"character":5},"end":{"line":50,"character":10}}}]}
  {"jsonrpc":"2.0","id":6,"result":{"contents":{"kind":"markdown","value":"```kanon\nrule b_not : Not sv\n```\n\n*bool.kn*"},"range":{"start":{"line":1,"character":21},"end":{"line":1,"character":26}}}}
  {"jsonrpc":"2.0","id":7,"result":[{"uri":"file://ROOT/lang.knl","range":{"start":{"line":8,"character":5},"end":{"line":8,"character":6}}}]}
  {"jsonrpc":"2.0","id":8,"result":{"contents":{"kind":"markdown","value":"```kanon\nsort TBool\n```\n\n*bool.knl*"},"range":{"start":{"line":1,"character":11},"end":{"line":1,"character":16}}}}
  {"jsonrpc":"2.0","id":9,"result":null}

Completion offers the names of the language and the keywords; the symbols of
the workspace include the rules of each rule function.

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 1 completion imp.kn 6 0)"
  > } > input
  $ lsp | grep -o '{"label":"\(neg\|b_imp\|b_not\|Imp\|implies\|ty\|rule\)"[^}]*}'
  {"label":"b_not","kind":3,"detail":"rule b_not : Not sv"}
  {"label":"neg","kind":3,"detail":"fn neg (a : t) : t"}
  {"label":"b_imp","kind":3,"detail":"rule b_imp : Imp (v1, v2)"}
  {"label":"Imp","kind":4,"detail":"node Imp : TBool -> TBool -> TBool"}
  {"label":"implies","kind":24,"detail":"infix \"implies\" = Imp, b_imp"}
  {"label":"ty","kind":7,"detail":"type ty"}
  {"label":"rule","kind":14}

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg '{"jsonrpc":"2.0","id":1,"method":"workspace/symbol","params":{"query":"IMP"}}'
  >   msg '{"jsonrpc":"2.0","id":2,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file://ROOT/more.kn"}}}'
  >   msg '{"jsonrpc":"2.0","id":3,"method":"kanon/unknown","params":{}}'
  > } > input
  $ lsp | grep -v publishDiagnostics
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"renameProvider":{"prepareProvider":true},"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true,"workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true}}},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","id":1,"result":[{"name":"b_imp","kind":12,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":3,"character":5},"end":{"line":3,"character":10}}}},{"name":"b_imp/false_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":4,"character":4},"end":{"line":4,"character":10}}},"containerName":"b_imp"},{"name":"b_imp/true_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}},"containerName":"b_imp"},{"name":"b_imp/not_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":6,"character":4},"end":{"line":6,"character":8}}},"containerName":"b_imp"},{"name":"Imp","kind":9,"location":{"uri":"file://ROOT/imp.knl","range":{"start":{"line":1,"character":5},"end":{"line":1,"character":8}}}},{"name":"implies","kind":25,"location":{"uri":"file://ROOT/imp.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":14}}}},{"name":"b_imp/same","kind":22,"location":{"uri":"file://ROOT/more.kn","range":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}}},"containerName":"b_imp"}]}
  {"jsonrpc":"2.0","id":2,"result":[{"name":"extend b_imp","detail":"extend rule b_imp before true_","kind":12,"range":{"start":{"line":0,"character":0},"end":{"line":1,"character":31}},"selectionRange":{"start":{"line":0,"character":12},"end":{"line":0,"character":17}},"children":[{"name":"same","detail":"same: x implies x -> v_true","kind":22,"range":{"start":{"line":1,"character":4},"end":{"line":1,"character":31}},"selectionRange":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}},"children":[]}]}]}
  {"jsonrpc":"2.0","id":3,"error":{"code":-32601,"message":"unknown method kanon/unknown"}}

Without shutdown, the end of the input is an error.

  $ msg "$init" > input
  $ kanon lsp < input > /dev/null
  [1]

Local names, in another language: loc/lang.knl uses the bool module and the
modules xor (xor.knl, xor.kn) and more (more.kn).

  $ mkdir loc
  $ cat > loc/lang.knl <<'KN'
  > use +bool
  > use "xor"
  > use "more"
  > 
  > type var [@ocaml "string"] [@noeq]
  > 
  > type t =
  >   | Var of var
  >   | Unop of unop * t [@operators]
  >   | Binop of binop * t * t [@operators]
  >   | Triop of triop * t * t * t [@operators]
  >   | Nop of nop * t list [@operators]
  > 
  > type unop
  > type binop
  > type triop
  > type nop = Distinct
  > type ty
  > KN
  $ cat > loc/xor.knl <<'KN'
  > node Int of int [@literal int]
  > node Xor : TBool -> TBool -> TBool [@unit false]
  > 
  > infix "xor" = Xor, b_xor
  > infix "+" = Or, b_or
  > KN
  $ cat > loc/xor.kn <<'KN'
  > fn both (a b : t) : t =
  >   let f (x : t) : t = not x in
  >   let y : t = f a in
  >   match b with
  >   | #k when k = 0 -> y
  >   | z -> z + y
  > 
  > rule b_xor : Xor (v1, v2) =
  >   | same: p xor p -> v_false
  >   | not_: not p xor q -> not (p xor q)
  >   | true_: _ xor true -> not v1
  > KN
  $ cat > loc/more.kn <<'KN'
  > extend rule b_xor
  >   before not_ =
  >   | false_l: false xor x -> x
  > KN
  $ initloc='{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/loc","capabilities":{}}}'

The definitions of a pattern variable (where it is first bound), of a let, of
a parameter, of a local function, of #k, and of an operand of the spec; then
the hovers of a let and of an operator in a pattern, and the definitions of
+ (from just after it), of an infix word and of not, which go to their
declarations; then before r, on the line after extend rule f, the f of
extend rule f, and the hover of an operand of the spec.

  $ {
  >   msg "$initloc"
  >   msg "$(open loc/xor.kn "$(sed 's/$/\\n/' loc/xor.kn | tr -d '\n')")"
  >   msg "$(at 1 definition loc/xor.kn 5 9)"
  >   msg "$(at 2 definition loc/xor.kn 5 13)"
  >   msg "$(at 3 definition loc/xor.kn 2 16)"
  >   msg "$(at 4 definition loc/xor.kn 2 14)"
  >   msg "$(at 5 definition loc/xor.kn 4 12)"
  >   msg "$(at 6 definition loc/xor.kn 10 29)"
  >   msg "$(at 7 hover loc/xor.kn 5 13)"
  >   msg "$(at 8 hover loc/xor.kn 8 13)"
  >   msg "$(at 9 definition loc/xor.kn 5 12)"
  >   msg "$(at 10 definition loc/xor.kn 9 16)"
  >   msg "$(at 11 definition loc/xor.kn 9 25)"
  >   msg "$(at 12 definition loc/more.kn 1 9)"
  >   msg "$(at 13 definition loc/more.kn 0 14)"
  >   msg "$(at 14 hover loc/xor.kn 10 29)"
  >   msg '{"jsonrpc":"2.0","id":15,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":5}}}]}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":2,"character":6},"end":{"line":2,"character":7}}}]}
  {"jsonrpc":"2.0","id":3,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":0,"character":9},"end":{"line":0,"character":10}}}]}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":1,"character":6},"end":{"line":1,"character":7}}}]}
  {"jsonrpc":"2.0","id":5,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":4,"character":5},"end":{"line":4,"character":6}}}]}
  {"jsonrpc":"2.0","id":6,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":7,"character":18},"end":{"line":7,"character":20}}}]}
  {"jsonrpc":"2.0","id":7,"result":{"contents":{"kind":"markdown","value":"```kanon\ny : t\n```\n\nVariable bound by `let`. Bound on line 3."},"range":{"start":{"line":5,"character":13},"end":{"line":5,"character":14}}}}
  {"jsonrpc":"2.0","id":8,"result":{"contents":{"kind":"markdown","value":"```kanon\ninfix \"xor\" = Xor, b_xor\n```\n\nIn this pattern, `a xor b` matches the node `Xor`.\n\n*xor.knl*"},"range":{"start":{"line":8,"character":12},"end":{"line":8,"character":15}}}}
  {"jsonrpc":"2.0","id":9,"result":[{"uri":"file://ROOT/loc/xor.knl","range":{"start":{"line":4,"character":7},"end":{"line":4,"character":8}}}]}
  {"jsonrpc":"2.0","id":10,"result":[{"uri":"file://ROOT/loc/xor.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":10}}}]}
  {"jsonrpc":"2.0","id":11,"result":[{"uri":"BUILTIN/bool.knl","range":{"start":{"line":15,"character":8},"end":{"line":15,"character":11}}}]}
  {"jsonrpc":"2.0","id":12,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":9,"character":4},"end":{"line":9,"character":8}}}]}
  {"jsonrpc":"2.0","id":13,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":7,"character":5},"end":{"line":7,"character":10}}}]}
  {"jsonrpc":"2.0","id":14,"result":{"contents":{"kind":"markdown","value":"```kanon\nv1 : t\n```\n\nParameter of the rule `b_xor`: an operand of its spec, `Xor`. Bound on line 8.\n\nA term of sort `TBool`."},"range":{"start":{"line":10,"character":29},"end":{"line":10,"character":31}}}}
  {"jsonrpc":"2.0","id":15,"result":null}

References and highlights: of a pattern variable, and of a function (with its
declaration), in the files of its language.

  $ refs() {
  >   printf '{"jsonrpc":"2.0","id":%s,"method":"textDocument/references","params":{"textDocument":{"uri":"file://ROOT/%s"},"position":{"line":%s,"character":%s},"context":{"includeDeclaration":true}}}' "$@"
  > }
  $ {
  >   msg "$initloc"
  >   msg "$(open loc/xor.kn "$(sed 's/$/\\n/' loc/xor.kn | tr -d '\n')")"
  >   msg "$(refs 1 loc/xor.kn 8 16)"
  >   msg "$(refs 2 loc/xor.kn 7 6)"
  >   msg "$(at 3 documentHighlight loc/xor.kn 1 9)"
  >   msg '{"jsonrpc":"2.0","id":4,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":[{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":8,"character":10},"end":{"line":8,"character":11}}},{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":8,"character":16},"end":{"line":8,"character":17}}}]}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/loc/more.kn","range":{"start":{"line":0,"character":12},"end":{"line":0,"character":17}}},{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":7,"character":5},"end":{"line":7,"character":10}}},{"uri":"file://ROOT/loc/xor.knl","range":{"start":{"line":3,"character":19},"end":{"line":3,"character":24}}}]}
  {"jsonrpc":"2.0","id":3,"result":[{"range":{"start":{"line":1,"character":9},"end":{"line":1,"character":10}},"kind":3},{"range":{"start":{"line":1,"character":26},"end":{"line":1,"character":27}},"kind":2}]}
  {"jsonrpc":"2.0","id":4,"result":null}

Renaming a local, then a function, in all the files of its language; a
function of the built-in modules and an uppercase function name are refused.

  $ rename() {
  >   printf '{"jsonrpc":"2.0","id":%s,"method":"textDocument/rename","params":{"textDocument":{"uri":"file://ROOT/%s"},"position":{"line":%s,"character":%s},"newName":"%s"}}' "$@"
  > }
  $ {
  >   msg "$initloc"
  >   msg "$(open loc/xor.kn "$(sed 's/$/\\n/' loc/xor.kn | tr -d '\n')")"
  >   msg "$(at 1 prepareRename loc/xor.kn 9 14)"
  >   msg "$(rename 2 loc/xor.kn 9 14 r)"
  >   msg "$(rename 3 loc/xor.kn 7 6 b_exclusive_or)"
  >   msg "$(rename 4 loc/xor.kn 8 21 false_value)"
  >   msg "$(rename 5 loc/xor.kn 7 6 Bxor)"
  >   msg '{"jsonrpc":"2.0","id":6,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":{"range":{"start":{"line":9,"character":14},"end":{"line":9,"character":15}},"placeholder":"p"}}
  {"jsonrpc":"2.0","id":2,"result":{"changes":{"file://ROOT/loc/xor.kn":[{"range":{"start":{"line":9,"character":14},"end":{"line":9,"character":15}},"newText":"r"},{"range":{"start":{"line":9,"character":30},"end":{"line":9,"character":31}},"newText":"r"}]}}}
  {"jsonrpc":"2.0","id":3,"result":{"changes":{"file://ROOT/loc/more.kn":[{"range":{"start":{"line":0,"character":12},"end":{"line":0,"character":17}},"newText":"b_exclusive_or"}],"file://ROOT/loc/xor.kn":[{"range":{"start":{"line":7,"character":5},"end":{"line":7,"character":10}},"newText":"b_exclusive_or"}],"file://ROOT/loc/xor.knl":[{"range":{"start":{"line":3,"character":19},"end":{"line":3,"character":24}},"newText":"b_exclusive_or"}]}}}
  {"jsonrpc":"2.0","id":4,"error":{"code":-32803,"message":"v_false is in the built-in module bool.kn, which cannot be edited"}}
  {"jsonrpc":"2.0","id":5,"error":{"code":-32803,"message":"Bxor is not a valid name: names start with a lowercase letter or _"}}
  {"jsonrpc":"2.0","id":6,"result":null}

The errors of independent functions are reported together; a name defined
twice is reported at its second definition, and an unknown rule after before
at its name.

  $ {
  >   msg "$initloc"
  >   msg "$(open loc/xor.kn "$(sed -e 's/z + y/z + 1/' -e 's/not v1/not 1/' -e 's/$/\\n/' loc/xor.kn | tr -d '\n')")"
  >   msg "$(at 1 hover loc/xor.kn 0 0)"
  >   msg "$(change loc/xor.kn "$(sed 's/$/\\n/' loc/xor.kn | tr -d '\n')fn both (a : t) : t = a\\n")"
  >   msg "$(at 2 hover loc/xor.kn 0 0)"
  >   msg "$(change loc/xor.kn "$(sed 's/$/\\n/' loc/xor.kn | tr -d '\n')")"
  >   msg "$(open loc/more.kn "$(sed -e 's/not_/nope/' -e 's/$/\\n/' loc/more.kn | tr -d '\n')")"
  >   msg '{"jsonrpc":"2.0","id":3,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/xor.kn","diagnostics":[{"range":{"start":{"line":5,"character":13},"end":{"line":5,"character":14}},"severity":1,"source":"kanon","message":"type mismatch: expected t, got int"},{"range":{"start":{"line":10,"character":29},"end":{"line":10,"character":30}},"severity":1,"source":"kanon","message":"type mismatch: expected bool, got int"}]}}
  {"jsonrpc":"2.0","id":1,"result":null}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/xor.kn","diagnostics":[{"range":{"start":{"line":11,"character":3},"end":{"line":11,"character":7}},"severity":1,"source":"kanon","message":"both is defined twice"}]}}
  {"jsonrpc":"2.0","id":2,"result":null}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/more.kn","diagnostics":[{"range":{"start":{"line":1,"character":9},"end":{"line":1,"character":13}},"severity":1,"source":"kanon","message":"extend b_xor: b_xor has no rule nope"}]}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/xor.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","id":3,"result":null}

The server watches the files of the workspace when the client can: a module
created on disk is then found.

  $ initwatch='{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/loc","capabilities":{"workspace":{"didChangeWatchedFiles":{"dynamicRegistration":true}}}}}'
  $ {
  >   msg "$initwatch"
  >   msg '{"jsonrpc":"2.0","method":"initialized","params":{}}'
  >   msg "$(open loc/more.kn "use \\\"extra\\\"\\n$(sed 's/$/\\n/' loc/more.kn | tr -d '\n')")"
  >   msg "$(at 1 hover loc/more.kn 0 0)"
  >   sleep 1
  >   echo 'fn extra (x : t) : t = x' > loc/extra.kn
  >   msg '{"jsonrpc":"2.0","method":"workspace/didChangeWatchedFiles","params":{"changes":[{"uri":"file://ROOT/loc/extra.kn","type":1}]}}'
  >   msg '{"jsonrpc":"2.0","id":2,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } | kanon lsp |
  >   sed -e 's/Content-Length: [0-9]*\r$//' -e '/^\r*$/d' -e "s|$PWD|ROOT|g" |
  >   grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"method":"client/registerCapability","params":{"registrations":[{"id":"kanon-watched-files","method":"workspace/didChangeWatchedFiles","registerOptions":{"watchers":[{"globPattern":"**/*.{kn,knl}"}]}}]}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/more.kn","diagnostics":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":11}},"severity":1,"source":"kanon","message":"use \"extra\": no ROOT/loc/extra.knl or ROOT/loc/extra.kn"}]}}
  {"jsonrpc":"2.0","id":1,"result":null}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/more.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","id":2,"result":null}
