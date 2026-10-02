# Kanon in a web page

`web/` compiles kanon, its command line and its language server, to
JavaScript with js_of_ocaml, for a web page to run it in a Web Worker: one
classic script, `kanon.js`, which defines the API `globalThis.kanon` below.

## Building

```
opam install js_of_ocaml-compiler js_of_ocaml zarith_stubs_js
dune build @web --profile web
```

builds `_build/default/web/dist/`, the directory to serve, which only has
`kanon.js` (it loads nothing else, so it can be served from any path). `web/`
is only built in the `web` profile: in the others (`dune build`, `dune test`,
`opam install`), it is left out, so kanon does not need js_of_ocaml, and
`dune build @web` says how to build it.

## Testing

```
dune build --profile web && node web/test.mjs
```

loads `kanon.js` in node as a worker does, checks `kanon.run` against the
native `kanon` on `examples/bool`, `test/tiny.t` and errors, and a session of
the language server on `test/lsp.t` against `kanon lsp`. With soteria
(`SOTERIA=path/to/soteria/soteria`), it also checks that `kanon.run` agrees
with `kanon` on its language `Bv_values` with every backend, and reports the
time of the check of `Bv_values` by the language server.

## The API

A worker loads `kanon.js` with `importScripts`; it defines `globalThis.kanon`
and then calls `globalThis.onkanonready()`, if it is a function:

```js
self.onkanonready = () => { /* kanon is ready */ };
importScripts("dist/kanon.js");
const k = self.kanon;
k.writeFile(k.root + "/lang.knl", 'use builtin "bool"\n...');
k.lsp(JSON.stringify({ jsonrpc: "2.0", id: 0, method: "initialize",
  params: { rootUri: "file://" + k.root, capabilities: {} } }));
```

Strings are JavaScript strings, and paths are absolute paths of the file system
of the runtime (relative ones are relative to `kanon.root`).

```
kanon.version : string                       // git describe of the build, or "dev"
kanon.root : string                          // "/sandbox": the directory of the user's files
kanon.writeFile(path: string, contents: string): void   // create or replace (and the directories)
kanon.removeFile(path: string): void
kanon.readFile(path: string): string | null  // also the files that the server's locations point at
kanon.listFiles(dir: string): string[]       // the files under dir, recursively, absolute
kanon.lsp(message: string): string[]         // handles one JSON-RPC message; the messages sent
kanon.check(): string[]                      // runs the pending check; the messages sent
kanon.run(args: string[]): { code: number, stdout: string, stderr: string }  // kanon ARGS...
kanon.backends : string[]                    // the backends of run: ocaml, ..., lean-soundness
kanon.builtins : { [file: string]: string }  // the modules built into kanon: bool.knl, bool.kn
```

- `writeFile`, `removeFile` throw an `Error` if they fail; `lsp`, `check` and
  `run` do not throw.
- `lsp` handles a message as `kanon lsp` does, and returns the messages that
  the server sends meanwhile (responses and notifications), in order. Like
  `kanon lsp`, it checks the changed files before answering a request, but
  not after a notification: `check` does, as `kanon lsp` does once no message
  is waiting; the page calls it after a pause in the changes. The `exit`
  notification is ignored.
- `run(args)` is `kanon args` in `kanon.root`: its exit code and outputs. An
  exception is reported as by `kanon` (`Fatal error: exception ...`, code 2).

## The file system

The files are in memory, in devices of js_of_ocaml (in a browser as in node):
`/sandbox`, the root, and the directory where the language server writes the
built-in modules for its definitions in them
(`/tmp/kanon-modules-<digest>/bool.kn`, which `readFile` reads). In a
browser, the whole file system is in memory; `/sandbox` is a device of its
own so that it is in memory in node too (where `/` is the disk), for the
tests. The language server finds the roots of the workspace (`file:///sandbox`)
on it as on a disk: `stubs.js` gives the devices in memory the `stat` and
`lstat` that its scan of the workspace uses.

## js_of_ocaml, not wasm_of_ocaml

wasm_of_ocaml 6.4.1 is about 3 times as fast (the check of `Bv_values` in
node: 116 ms the first time and 53 ms after, against 362 and 185 ms with
js_of_ocaml; generating its OCaml: 70 against 230 ms), but it does not run
kanon in a worker as it is:

- Zarith has no Wasm implementation (`zarith_stubs_js` is for JavaScript).
- Its file system in a browser only has the files registered with
  `Sys_js.create_file`: they cannot be removed, written by `open_out`, or
  `lstat`ed, and there are no directories to create or change to, which the
  language server and `run` need.
- In a worker, it loads its `.wasm` relative to the worker's URL rather than
  to its script's.
- It needs WebAssembly GC and exception handling (recent browsers only).

js_of_ocaml (`--opt 3`) gives an 860 KB script (210 KB gzipped), which
loads in about 80 ms.
