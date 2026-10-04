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

  $ IMP='(* [neg a] is the negation of [a]. *)\nfn neg (a : t) : t = Bool.not_ a\n\nrule b_imp : Imp (v1, v2) =\n  | false_: false implies _ -> Bool.v_true\n  | true_: true implies x -> x\n  | not_: x implies false -> neg x\n'
  $ MORE='extend rule Imp.b_imp before true_ =\n  | same: x implies x -> Bool.v_true\n'
  $ {
  >   msg "$init"
  >   msg '{"jsonrpc":"2.0","method":"initialized","params":{}}'
  >   msg "$(open more.kn "$MORE")"
  >   msg "$(at 1 hover more.kn 0 30)"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 2 hover imp.kn 6 29)"
  >   msg "$(change imp.kn "$(printf '%s' "$IMP" | sed 's/Bool.not_ a/Bool.not_ a in/')")"
  >   msg "$(at 3 hover imp.kn 3 14)"
  >   msg "$(change imp.kn "$IMP")"
  >   msg "$(change more.kn "use \\\"missing\\\"\\n$MORE")"
  >   msg "$(at 4 definition more.kn 1 31)"
  >   msg "$(change more.kn "$MORE")"
  >   msg '{"jsonrpc":"2.0","id":5,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"renameProvider":{"prepareProvider":true},"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true,"workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true}}},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[{"range":{"start":{"line":1,"character":31},"end":{"line":1,"character":32}},"severity":1,"source":"kanon","message":"type mismatch: expected t, got int"}]}}
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nrule Imp.b_imp =\n  | true_: true implies x -> x\n```\n\n*imp.kn*"},"range":{"start":{"line":0,"character":29},"end":{"line":0,"character":34}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","id":2,"result":{"contents":{"kind":"markdown","value":"```kanon\nfn neg (a : t) : t\n```\n\n[neg a] is the negation of [a].\n\n*imp.kn*"},"range":{"start":{"line":6,"character":29},"end":{"line":6,"character":32}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[{"range":{"start":{"line":1,"character":33},"end":{"line":1,"character":35}},"severity":1,"source":"kanon","message":"syntax error"}]}}
  {"jsonrpc":"2.0","id":3,"result":{"contents":{"kind":"markdown","value":"```kanon\nnode Imp : TBool -> TBool -> TBool\n```\n\nImplication.\n\n*imp.knl*"},"range":{"start":{"line":3,"character":13},"end":{"line":3,"character":16}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/imp.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/more.kn","diagnostics":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":13}},"severity":1,"source":"kanon","message":"use \"missing\": no ROOT/missing.knl or ROOT/missing.kn"}]}}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}}]}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/more.kn","diagnostics":[]}}
  {"jsonrpc":"2.0","id":5,"result":null}

Navigation: the definitions of a function, a node, an operator, a rule after
before (in the function that extend extends), a function of the bool module,
built into kanon, which the server writes to a file, but not of the type of
terms t, which Kanon generates. Hover shows the header of the definition (here
of a sort), and the comment before it. The module of a use goes to its files,
and its hover shows its first comment; it cannot be renamed.

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 1 definition imp.kn 6 29)"
  >   msg "$(at 2 definition imp.kn 3 14)"
  >   msg "$(at 3 definition imp.kn 4 20)"
  >   msg "$(at 4 definition more.kn 0 30)"
  >   msg "$(at 5 definition imp.kn 1 27)"
  >   msg "$(at 6 hover imp.kn 1 27)"
  >   msg "$(at 7 definition imp.kn 1 12)"
  >   msg "$(at 8 hover imp.knl 1 12)"
  >   msg "$(at 9 definition lang.knl 2 14)"
  >   msg "$(at 10 hover lang.knl 2 14)"
  >   msg "$(at 11 definition lang.knl 3 6)"
  >   msg "$(printf '{"jsonrpc":"2.0","id":12,"method":"textDocument/rename","params":{"textDocument":{"uri":"file://ROOT/lang.knl"},"position":{"line":2,"character":14},"newName":"int"}}')"
  >   msg '{"jsonrpc":"2.0","id":13,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v publishDiagnostics
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"renameProvider":{"prepareProvider":true},"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true,"workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true}}},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","id":1,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":1,"character":3},"end":{"line":1,"character":6}}}]}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":1,"character":5},"end":{"line":1,"character":8}}}]}
  {"jsonrpc":"2.0","id":3,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":14}}}]}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}}]}
  {"jsonrpc":"2.0","id":5,"result":[{"uri":"BUILTIN/bool.kn","range":{"start":{"line":50,"character":5},"end":{"line":50,"character":9}}}]}
  {"jsonrpc":"2.0","id":6,"result":{"contents":{"kind":"markdown","value":"```kanon\nrule not_ : Not sv\n```\n\n*bool.kn*"},"range":{"start":{"line":1,"character":21},"end":{"line":1,"character":30}}}}
  {"jsonrpc":"2.0","id":7,"result":null}
  {"jsonrpc":"2.0","id":8,"result":{"contents":{"kind":"markdown","value":"```kanon\nsort TBool\n```\n\n*bool.knl*"},"range":{"start":{"line":1,"character":11},"end":{"line":1,"character":16}}}}
  {"jsonrpc":"2.0","id":9,"result":[{"uri":"BUILTIN/bool.knl","range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}}},{"uri":"BUILTIN/bool.kn","range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}}}]}
  {"jsonrpc":"2.0","id":10,"result":{"contents":{"kind":"markdown","value":"```kanon\nuse builtin \"bool\"\n```\n\nThe bool module, at the bottom of every language: booleans, equality, [Ite]\nand [Distinct]. See the README of Kanon for the syntax.\n\n*bool.knl*"},"range":{"start":{"line":2,"character":13},"end":{"line":2,"character":17}}}}
  {"jsonrpc":"2.0","id":11,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}}},{"uri":"file://ROOT/imp.kn","range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}}}]}
  {"jsonrpc":"2.0","id":12,"error":{"code":-32803,"message":"modules cannot be renamed"}}
  {"jsonrpc":"2.0","id":13,"result":null}

Completion offers the names of the language and the keywords; the symbols of
the workspace include the rules of each rule function.

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 1 completion imp.kn 6 0)"
  > } > input
  $ lsp | grep -o '{"label":"\(neg\|b_imp\|Bool.not_\|Imp\|implies\|var\|rule\)"[^}]*}'
  {"label":"Bool.not_","kind":3,"detail":"rule not_ : Not sv"}
  {"label":"neg","kind":3,"detail":"fn neg (a : t) : t"}
  {"label":"b_imp","kind":3,"detail":"rule b_imp : Imp (v1, v2)"}
  {"label":"Imp","kind":4,"detail":"node Imp : TBool -> TBool -> TBool"}
  {"label":"implies","kind":24,"detail":"infix \"implies\" = Imp, b_imp"}
  {"label":"var","kind":7,"detail":"type var [@ocaml \"string\"] [@noeq]"}
  {"label":"rule","kind":14}

A name of another module is qualified: after `Bool.`, the names of the module
Bool, plain; elsewhere, those of the other modules with their module, and the
names of the module of the file plain. The modules are completed too.

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$(printf '%s' "$IMP" | sed 's/Bool.not_ a/Bool.n/')")"
  >   msg "$(at 1 completion imp.kn 1 27)"
  >   msg "$(at 2 completion imp.kn 3 0)"
  > } > input
  $ lsp | grep '"id":1,' | grep -o '{"label":"\(not_\|ite\|neg\|Bool.not_\)"'
  {"label":"not_"
  {"label":"ite"
  $ lsp | grep '"id":2,' | grep -o '{"label":"\(not_\|neg\|b_imp\|Bool.not_\|Bool\)"'
  {"label":"Bool.not_"
  {"label":"Bool"
  {"label":"neg"
  {"label":"b_imp"

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg '{"jsonrpc":"2.0","id":1,"method":"workspace/symbol","params":{"query":"IMP"}}'
  >   msg '{"jsonrpc":"2.0","id":2,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file://ROOT/more.kn"}}}'
  >   msg '{"jsonrpc":"2.0","id":3,"method":"kanon/unknown","params":{}}'
  > } > input
  $ lsp | grep -v publishDiagnostics
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"renameProvider":{"prepareProvider":true},"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true,"workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true}}},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","id":1,"result":[{"name":"b_imp","kind":12,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":3,"character":5},"end":{"line":3,"character":10}}}},{"name":"b_imp/false_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":4,"character":4},"end":{"line":4,"character":10}}},"containerName":"Imp.b_imp"},{"name":"b_imp/true_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}},"containerName":"Imp.b_imp"},{"name":"b_imp/not_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":6,"character":4},"end":{"line":6,"character":8}}},"containerName":"Imp.b_imp"},{"name":"Imp","kind":9,"location":{"uri":"file://ROOT/imp.knl","range":{"start":{"line":1,"character":5},"end":{"line":1,"character":8}}}},{"name":"implies","kind":25,"location":{"uri":"file://ROOT/imp.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":14}}}},{"name":"b_imp/same","kind":22,"location":{"uri":"file://ROOT/more.kn","range":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}}},"containerName":"Imp.b_imp"}]}
  {"jsonrpc":"2.0","id":2,"result":[{"name":"extend Imp.b_imp","detail":"extend rule Imp.b_imp before true_","kind":12,"range":{"start":{"line":0,"character":0},"end":{"line":1,"character":36}},"selectionRange":{"start":{"line":0,"character":12},"end":{"line":0,"character":21}},"children":[{"name":"same","detail":"same: x implies x -> Bool.v_true","kind":22,"range":{"start":{"line":1,"character":4},"end":{"line":1,"character":36}},"selectionRange":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}},"children":[]}]}]}
  {"jsonrpc":"2.0","id":3,"error":{"code":-32601,"message":"unknown method kanon/unknown"}}

Without shutdown, the end of the input is an error.

  $ msg "$init" > input
  $ kanon lsp < input > /dev/null
  [1]

Local names, in another language: loc/lang.knl uses the bool module and the
modules xor (xor.knl, xor.kn) and more (more.kn).

  $ mkdir loc
  $ cat > loc/lang.knl <<'KN'
  > use builtin "bool"
  > use "xor"
  > use "more"
  > 
  > type var [@ocaml "string"] [@noeq]
  > 
  > node Var of var
  > KN
  $ cat > loc/xor.knl <<'KN'
  > node Int of int
  > node Xor : TBool -> TBool -> TBool [@unit false]
  > 
  > infix "xor" = Xor, b_xor
  > infix "+" = Or, Bool.or_
  > KN
  $ cat > loc/xor.kn <<'KN'
  > fn both (a b : t) : t =
  >   let f (x : t) : t = not x in
  >   let y : t = f a in
  >   match b with
  >   | #k when k -> y
  >   | z -> z + y
  > 
  > rule b_xor : Xor (v1, v2) =
  >   | same: p xor p -> Bool.v_false
  >   | not_: not p xor q -> not (p xor q)
  >   | true_: _ xor true -> not v1
  > KN
  $ cat > loc/more.kn <<'KN'
  > extend rule Xor.b_xor
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
  >   msg "$(at 13 definition loc/more.kn 0 18)"
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
  {"jsonrpc":"2.0","id":11,"result":[{"uri":"BUILTIN/bool.knl","range":{"start":{"line":16,"character":8},"end":{"line":16,"character":11}}}]}
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
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/loc/more.kn","range":{"start":{"line":0,"character":12},"end":{"line":0,"character":21}}},{"uri":"file://ROOT/loc/xor.kn","range":{"start":{"line":7,"character":5},"end":{"line":7,"character":10}}},{"uri":"file://ROOT/loc/xor.knl","range":{"start":{"line":3,"character":19},"end":{"line":3,"character":24}}}]}
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
  >   msg "$(rename 4 loc/xor.kn 8 26 false_value)"
  >   msg "$(rename 5 loc/xor.kn 7 6 Bxor)"
  >   msg '{"jsonrpc":"2.0","id":6,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":{"range":{"start":{"line":9,"character":14},"end":{"line":9,"character":15}},"placeholder":"p"}}
  {"jsonrpc":"2.0","id":2,"result":{"changes":{"file://ROOT/loc/xor.kn":[{"range":{"start":{"line":9,"character":14},"end":{"line":9,"character":15}},"newText":"r"},{"range":{"start":{"line":9,"character":30},"end":{"line":9,"character":31}},"newText":"r"}]}}}
  {"jsonrpc":"2.0","id":3,"result":{"changes":{"file://ROOT/loc/more.kn":[{"range":{"start":{"line":0,"character":16},"end":{"line":0,"character":21}},"newText":"b_exclusive_or"}],"file://ROOT/loc/xor.kn":[{"range":{"start":{"line":7,"character":5},"end":{"line":7,"character":10}},"newText":"b_exclusive_or"}],"file://ROOT/loc/xor.knl":[{"range":{"start":{"line":3,"character":19},"end":{"line":3,"character":24}},"newText":"b_exclusive_or"}]}}}
  {"jsonrpc":"2.0","id":4,"error":{"code":-32803,"message":"Bool.v_false is in the built-in module bool.kn, which cannot be edited"}}
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
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/xor.kn","diagnostics":[{"range":{"start":{"line":11,"character":3},"end":{"line":11,"character":7}},"severity":1,"source":"kanon","message":"Xor.both is defined twice"}]}}
  {"jsonrpc":"2.0","id":2,"result":null}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/loc/more.kn","diagnostics":[{"range":{"start":{"line":1,"character":9},"end":{"line":1,"character":13}},"severity":1,"source":"kanon","message":"extend Xor.b_xor: Xor.b_xor has no rule nope"}]}}
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

An operator with a word suffix is one operator, with the hover and the
definition of its declaration, in a pattern and in an expression; a doc comment
is the documentation of the hover of what it documents, and the diagnostics
tell where an operator is not surrounded by spaces.

  $ mkdir suf
  $ cat > suf/lang.knl <<'KN'
  > use builtin "bool"
  > use "ops"
  > KN
  $ cat > suf/ops.knl <<'KN'
  > node Ult : TBool -> TBool -> TBool
  > infix "<u" = Ult, b_ult
  > KN
  $ cat > suf/ops.kn <<'KN'
  > (** Strictly below. *)
  > fn below (a b : t) : t = a <u b
  > rule b_ult : Ult (v1, v2) =
  >   | same: p <u p -> Bool.v_false
  > KN
  $ initsuf='{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/suf","capabilities":{}}}'
  $ {
  >   msg "$initsuf"
  >   msg "$(open suf/ops.kn "$(sed 's/$/\\n/' suf/ops.kn | tr -d '\n')")"
  >   msg "$(at 1 hover suf/ops.kn 1 28)"
  >   msg "$(at 2 definition suf/ops.kn 1 27)"
  >   msg "$(at 3 hover suf/ops.kn 3 12)"
  >   msg "$(at 4 definition suf/ops.kn 3 13)"
  >   msg "$(at 5 hover suf/ops.kn 1 4)"
  >   msg "$(change suf/ops.kn "$(sed -e 's/a <u b/a<u b/' -e 's/$/\\n/' suf/ops.kn | tr -d '\n')")"
  >   msg '{"jsonrpc":"2.0","id":6,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\ninfix \"<u\" = Ult, b_ult\n```\n\n`a <u b` is `b_ult a b` on terms; in patterns, it matches the node `Ult`.\n\n*ops.knl*"},"range":{"start":{"line":1,"character":27},"end":{"line":1,"character":29}}}}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/suf/ops.knl","range":{"start":{"line":1,"character":7},"end":{"line":1,"character":9}}}]}
  {"jsonrpc":"2.0","id":3,"result":{"contents":{"kind":"markdown","value":"```kanon\ninfix \"<u\" = Ult, b_ult\n```\n\nIn this pattern, `a <u b` matches the node `Ult`.\n\n*ops.knl*"},"range":{"start":{"line":3,"character":12},"end":{"line":3,"character":14}}}}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/suf/ops.knl","range":{"start":{"line":1,"character":7},"end":{"line":1,"character":9}}}]}
  {"jsonrpc":"2.0","id":5,"result":{"contents":{"kind":"markdown","value":"```kanon\nfn below (a b : t) : t\n```\n\nStrictly below.\n\n*ops.kn*"},"range":{"start":{"line":1,"character":3},"end":{"line":1,"character":8}}}}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/suf/ops.kn","diagnostics":[{"range":{"start":{"line":1,"character":26},"end":{"line":1,"character":27}},"severity":1,"source":"kanon","message":"the operator < must be surrounded by spaces"}]}}
  {"jsonrpc":"2.0","id":6,"result":null}

A node built at a computed sort: the names of the sort are resolved like the
others, with the hover and the definition of a function and of a parameter, and
a sort that is not a ty is reported where it is.

  $ mkdir cs
  $ cat > cs/lang.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > node Field of int * t
  > KN
  $ cat > cs/rules.kn <<'KN'
  > (** The sort of the field [i] of [v]. *)
  > fn field_ty (v : t) (i : int) : ty = TInt
  > fn mk (i : int) (v : t) (s : ty) : t = (Field (i, v) : field_ty v i)
  > fn mk_in (i : int) (v : t) (s : ty) : t = (Field (i, v) : s)
  > KN
  $ initcs='{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/cs","capabilities":{}}}'
  $ {
  >   msg "$initcs"
  >   msg "$(open cs/rules.kn "$(sed 's/$/\\n/' cs/rules.kn | tr -d '\n')")"
  >   msg "$(at 1 hover cs/rules.kn 2 57)"
  >   msg "$(at 2 definition cs/rules.kn 2 57)"
  >   msg "$(at 3 definition cs/rules.kn 2 66)"
  >   msg "$(at 4 definition cs/rules.kn 3 58)"
  >   msg "$(change cs/rules.kn "$(sed -e 's/: s)/: i)/' -e 's/$/\\n/' cs/rules.kn | tr -d '\n')")"
  >   msg '{"jsonrpc":"2.0","id":5,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nfn field_ty (v : t) (i : int) : ty\n```\n\nThe sort of the field [i] of [v].\n\n*rules.kn*"},"range":{"start":{"line":2,"character":55},"end":{"line":2,"character":63}}}}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/cs/rules.kn","range":{"start":{"line":1,"character":3},"end":{"line":1,"character":11}}}]}
  {"jsonrpc":"2.0","id":3,"result":[{"uri":"file://ROOT/cs/rules.kn","range":{"start":{"line":2,"character":7},"end":{"line":2,"character":8}}}]}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/cs/rules.kn","range":{"start":{"line":3,"character":28},"end":{"line":3,"character":29}}}]}
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/cs/rules.kn","diagnostics":[{"range":{"start":{"line":3,"character":58},"end":{"line":3,"character":59}},"severity":1,"source":"kanon","message":"type mismatch: expected ty, got int"}]}}
  {"jsonrpc":"2.0","id":5,"result":null}

Arrays: the hover of the type and of the functions on arrays, which Kanon
defines, the completion of these functions, the types of the elements and of
the indices that are checked, and a function of the language that cannot take
their names.

  $ mkdir ar
  $ cat > ar/lang.knl <<'KN'
  > sort TInt
  > node Int of int : TInt
  > KN
  $ cat > ar/rules.kn <<'KN'
  > fn first (a : int array) : int = array_get a 0
  > fn put (a : int array) (x : int) : int array = array_set a 0 x
  > fn lit : int array = [| 1; 2 |]
  > fn bad (a : int array) : int = array_get a true
  > fn other (a : int array) : int array = [| 1; true |]
  > KN
  $ initar='{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/ar","capabilities":{}}}'
  $ {
  >   msg "$initar"
  >   msg "$(open ar/rules.kn "$(sed 's/$/\\n/' ar/rules.kn | tr -d '\n')")"
  >   msg "$(at 1 hover ar/rules.kn 0 19)"
  >   msg "$(at 2 hover ar/rules.kn 0 38)"
  >   msg "$(at 3 hover ar/rules.kn 0 44)"
  >   msg "$(at 4 definition ar/rules.kn 1 57)"
  >   msg "$(at 5 completion ar/rules.kn 2 20)"
  >   msg '{"jsonrpc":"2.0","id":6,"method":"textDocument/rename","params":{"textDocument":{"uri":"file://ROOT/ar/rules.kn"},"position":{"line":1,"character":4},"newName":"array_get"}}'
  >   msg '{"jsonrpc":"2.0","id":7,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v -e '"id":0,' -e '"id":5,'
  {"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file://ROOT/ar/rules.kn","diagnostics":[{"range":{"start":{"line":3,"character":43},"end":{"line":3,"character":47}},"severity":1,"source":"kanon","message":"type mismatch: expected int, got bool"},{"range":{"start":{"line":4,"character":45},"end":{"line":4,"character":49}},"severity":1,"source":"kanon","message":"type mismatch: expected int, got bool"}]}}
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\ntype 'a array\n```\n\nAn immutable array, `[| a; b |]`, in OCaml `Iarray.t` and in Lean `Array`. `=` compares arrays element by element.\n\n*built into Kanon*"},"range":{"start":{"line":0,"character":18},"end":{"line":0,"character":23}}}}
  {"jsonrpc":"2.0","id":2,"result":{"contents":{"kind":"markdown","value":"```kanon\narray_get : 'a array -> int -> 'a\n```\n\nThe element at an index, which must be in bounds.\n\n*built into Kanon*"},"range":{"start":{"line":0,"character":33},"end":{"line":0,"character":42}}}}
  {"jsonrpc":"2.0","id":3,"result":{"contents":{"kind":"markdown","value":"```kanon\na : int array\n```\n\nParameter of `first`. Bound on line 1."},"range":{"start":{"line":0,"character":43},"end":{"line":0,"character":44}}}}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/ar/rules.kn","range":{"start":{"line":1,"character":8},"end":{"line":1,"character":9}}}]}
  {"jsonrpc":"2.0","id":6,"error":{"code":-32803,"message":"array_get is already a function"}}
  {"jsonrpc":"2.0","id":7,"result":null}
  $ lsp | grep '"id":5,' | grep -o '"label":"array_[a-z_]*","kind":3,"detail":"[^"]*"'
  "label":"array_length","kind":3,"detail":"array_length : 'a array -> int"
  "label":"array_get","kind":3,"detail":"array_get : 'a array -> int -> 'a"
  "label":"array_set","kind":3,"detail":"array_set : 'a array -> int -> 'a -> 'a array"
  "label":"array_of_list","kind":3,"detail":"array_of_list : 'a list -> 'a array"
  "label":"array_to_list","kind":3,"detail":"array_to_list : 'a array -> 'a list"

A subsort has a hover, a definition and an outline entry, like a sort:

  $ mkdir sub
  $ printf 'sort TBitVector of nat\nsubsort TNonzero of nat : TBitVector n\nnode Div : TBitVector n -> TNonzero n -> TBitVector n\n' > sub/sub.knl
  $ {
  >   msg '{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/sub","capabilities":{}}}'
  >   msg '{"jsonrpc":"2.0","method":"initialized","params":{}}'
  >   msg "$(open sub/sub.knl 'sort TBitVector of nat\nsubsort TNonzero of nat : TBitVector n\nnode Div : TBitVector n -> TNonzero n -> TBitVector n\n')"
  >   msg "$(at 1 hover sub/sub.knl 2 29)"
  >   msg "$(at 2 definition sub/sub.knl 2 29)"
  >   msg '{"jsonrpc":"2.0","id":3,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } | kanon lsp |
  >   sed -e 's/Content-Length: [0-9]*\r$//' -e '/^\r*$/d' -e "s|$PWD|ROOT|g" |
  >   grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nsubsort TNonzero of nat : TBitVector n\n```\n\n*sub.knl*"},"range":{"start":{"line":2,"character":27},"end":{"line":2,"character":35}}}}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/sub/sub.knl","range":{"start":{"line":1,"character":8},"end":{"line":1,"character":16}}}]}
  {"jsonrpc":"2.0","id":3,"result":null}

Its doc comment and its Lean predicate are in the hover, the parent is a hover
and a definition of its own, `subsort` is a keyword to complete, a subsort is
completed with the sorts, and a declaration that does not check is reported on
the subsort:

  $ {
  >   msg '{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/sub","capabilities":{}}}'
  >   msg '{"jsonrpc":"2.0","method":"initialized","params":{}}'
  >   msg "$(open sub/doc.knl 'sort TBitVector of nat\n(** Not zero. *)\nsubsort TNonzero of nat : TBitVector n [@lean \"Nonzero\"]\n')"
  >   msg "$(at 1 hover sub/doc.knl 2 10)"
  >   msg "$(at 2 hover sub/doc.knl 2 30)"
  >   msg "$(at 3 completion sub/doc.knl 3 0)"
  >   msg "$(open sub/bad.knl 'sort TBitVector of nat\nsubsort A of int : TBitVector n\n')"
  >   msg '{"jsonrpc":"2.0","id":4,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } | kanon lsp |
  >   sed -e 's/Content-Length: [0-9]*\r$//' -e '/^\r*$/d' -e "s|$PWD|ROOT|g" |
  >   grep -v '"id":0,' | grep -o '"id":[12],"result":{"contents":{"kind":"markdown","value":"[^"]*\(\\"[^"]*\)*"\|{"label":"\(TNonzero\|subsort\)"[^}]*}\|"message":"[^"]*"'
  "id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nsubsort TNonzero of nat : TBitVector n [@lean \"Nonzero\"]\n```\n\nNot zero.\n\n*doc.knl*"
  "id":2,"result":{"contents":{"kind":"markdown","value":"```kanon\nsort TBitVector of nat\n```\n\n*doc.knl*"
  {"label":"TNonzero","kind":4,"detail":"subsort TNonzero of nat : TBitVector n [@lean \"Nonzero\"]"}
  {"label":"subsort","kind":14}
  "message":"subsort A: its arguments must be those of TBitVector (nat)"

The attributes of the typed backend: `[@@@ocaml_rules]` is a floating attribute
like `[@@@ocaml_prims]`. A node has a hover and a definition like any node,
and `[@ctor]`, which is gone, is an unknown attribute:

  $ mkdir typed
  $ {
  >   msg '{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/typed","capabilities":{}}}'
  >   msg '{"jsonrpc":"2.0","method":"initialized","params":{}}'
  >   msg "$(open typed/ok.knl '[@@@ocaml_rules \"Rules\"]\nsort TInt\nnode Int of int : TInt\nnode Neg : TInt -> TInt\n')"
  >   msg "$(at 1 hover typed/ok.knl 2 6)"
  >   msg "$(at 2 definition typed/ok.knl 2 6)"
  >   msg "$(open typed/ctor.knl 'sort TInt\nnode Int of int : TInt [@ctor mk_int]\n')"
  >   msg '{"jsonrpc":"2.0","id":3,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } | kanon lsp |
  >   sed -e 's/Content-Length: [0-9]*\r$//' -e '/^\r*$/d' -e "s|$PWD|ROOT|g" |
  >   grep -v '"id":0,' | grep -o '"id":[12],"result":{"contents":{"kind":"markdown","value":"[^"]*\(\\"[^"]*\)*"\|"id":2,"result":.*\|"message":"[^"]*"'
  "id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nnode Int of int : TInt\n```\n\n*ok.knl*"
  "id":2,"result":[{"uri":"file://ROOT/typed/ok.knl","range":{"start":{"line":2,"character":5},"end":{"line":2,"character":8}}}]}
  "message":"unknown attribute [@ctor]"

The sort of the result of a function, `: TBv n`, is resolved like the sort of a
parameter: the sort has a hover, and its variable goes to where the parameters
bind it.

  $ mkdir rs
  $ printf 'sort TBv of nat\nnode Neg : TBv n -> TBv n\n' > rs/lang.knl
  $ {
  >   msg '{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"rootUri":"file://ROOT/rs","capabilities":{}}}'
  >   msg "$(open rs/rules.kn 'fn keep (v : TBv n) : TBv n = v\n')"
  >   msg "$(at 1 hover rs/rules.kn 0 23)"
  >   msg "$(at 2 definition rs/rules.kn 0 26)"
  >   msg '{"jsonrpc":"2.0","id":3,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v '"id":0,'
  {"jsonrpc":"2.0","id":1,"result":{"contents":{"kind":"markdown","value":"```kanon\nsort TBv of nat\n```\n\n*lang.knl*"},"range":{"start":{"line":0,"character":22},"end":{"line":0,"character":25}}}}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/rs/rules.kn","range":{"start":{"line":0,"character":17},"end":{"line":0,"character":18}}}]}
  {"jsonrpc":"2.0","id":3,"result":null}
