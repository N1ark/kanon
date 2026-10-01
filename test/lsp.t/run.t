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
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true},"serverInfo":{"name":"kanon"}}}
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
before (in the function that extend extends), and a function of the bool
module, built into kanon, which the server writes to a file. Hover shows the
header of the definition, and the comment before it.

  $ {
  >   msg "$init"
  >   msg "$(open imp.kn "$IMP")"
  >   msg "$(at 1 definition imp.kn 6 29)"
  >   msg "$(at 2 definition imp.kn 3 14)"
  >   msg "$(at 3 definition imp.kn 4 20)"
  >   msg "$(at 4 definition more.kn 0 26)"
  >   msg "$(at 5 definition imp.kn 1 23)"
  >   msg "$(at 6 hover imp.kn 1 23)"
  >   msg '{"jsonrpc":"2.0","id":7,"method":"shutdown"}'
  >   msg '{"jsonrpc":"2.0","method":"exit"}'
  > } > input
  $ lsp | grep -v publishDiagnostics
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","id":1,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":1,"character":3},"end":{"line":1,"character":6}}}]}
  {"jsonrpc":"2.0","id":2,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":1,"character":5},"end":{"line":1,"character":8}}}]}
  {"jsonrpc":"2.0","id":3,"result":[{"uri":"file://ROOT/imp.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":14}}}]}
  {"jsonrpc":"2.0","id":4,"result":[{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}}]}
  {"jsonrpc":"2.0","id":5,"result":[{"uri":"BUILTIN/bool.kn","range":{"start":{"line":53,"character":5},"end":{"line":53,"character":10}}}]}
  {"jsonrpc":"2.0","id":6,"result":{"contents":{"kind":"markdown","value":"```kanon\nrule b_not : Not sv\n```\n\n*bool.kn*"},"range":{"start":{"line":1,"character":21},"end":{"line":1,"character":26}}}}
  {"jsonrpc":"2.0","id":7,"result":null}

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
  {"jsonrpc":"2.0","id":0,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":false}},"definitionProvider":true,"hoverProvider":true,"completionProvider":{},"workspaceSymbolProvider":true,"documentSymbolProvider":true},"serverInfo":{"name":"kanon"}}}
  {"jsonrpc":"2.0","id":1,"result":[{"name":"b_imp","kind":12,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":3,"character":5},"end":{"line":3,"character":10}}}},{"name":"b_imp/false_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":4,"character":4},"end":{"line":4,"character":10}}},"containerName":"b_imp"},{"name":"b_imp/true_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":5,"character":4},"end":{"line":5,"character":9}}},"containerName":"b_imp"},{"name":"b_imp/not_","kind":22,"location":{"uri":"file://ROOT/imp.kn","range":{"start":{"line":6,"character":4},"end":{"line":6,"character":8}}},"containerName":"b_imp"},{"name":"Imp","kind":9,"location":{"uri":"file://ROOT/imp.knl","range":{"start":{"line":1,"character":5},"end":{"line":1,"character":8}}}},{"name":"implies","kind":25,"location":{"uri":"file://ROOT/imp.knl","range":{"start":{"line":3,"character":7},"end":{"line":3,"character":14}}}},{"name":"b_imp/same","kind":22,"location":{"uri":"file://ROOT/more.kn","range":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}}},"containerName":"b_imp"}]}
  {"jsonrpc":"2.0","id":2,"result":[{"name":"extend b_imp","detail":"extend rule b_imp before true_","kind":12,"range":{"start":{"line":0,"character":0},"end":{"line":1,"character":31}},"selectionRange":{"start":{"line":0,"character":12},"end":{"line":0,"character":17}},"children":[{"name":"same","detail":"same: x implies x -> v_true","kind":22,"range":{"start":{"line":1,"character":4},"end":{"line":1,"character":31}},"selectionRange":{"start":{"line":1,"character":4},"end":{"line":1,"character":8}},"children":[]}]}]}
  {"jsonrpc":"2.0","id":3,"error":{"code":-32601,"message":"unknown method kanon/unknown"}}

Without shutdown, the end of the input is an error.

  $ msg "$init" > input
  $ kanon lsp < input > /dev/null
  [1]
