// The test of the web runtime of kanon, _build/default/web/dist/kanon.js, in
// node: dune build --profile web && node web/test.mjs
//
// It loads kanon.js as a Web Worker does, and checks that kanon.run prints the
// parts of the generated code that the native kanon writes (kanon ocaml and
// kanon lean, see site/scripts/parts.mjs) on the same files, and that the
// language server works as natively. With soteria (by default next
// to this repository, or at $SOTERIA), it also checks its language Bv_values
// and reports the time of that check.
//
// node web/test.mjs [path/to/kanon.js]

import vm from "node:vm";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { backends as partBackends, nativeParts, usage } from "../site/scripts/parts.mjs";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const script = path.resolve(
  process.argv[2] ?? path.join(repo, "_build/default/web/dist/kanon.js"),
);
const native = path.join(repo, "_build/default/src/main.exe");
const soteria = path.resolve(
  process.env.SOTERIA ?? path.join(repo, "../n1ark/soteria/soteria"),
);

let failures = 0;
let checks = 0;
function check(ok, what, detail) {
  checks++;
  if (!ok) {
    failures++;
    console.log(`FAIL: ${what}`);
    if (detail !== undefined) console.log(String(detail).slice(0, 2000));
  }
}
function same(actual, expected, what) {
  const a = JSON.stringify(actual);
  const e = JSON.stringify(expected);
  check(a === e, what, a === e ? undefined : `expected ${e}\n     got ${a}`);
}

for (const f of [script, native])
  if (!fs.existsSync(f)) {
    console.error(`${f} is missing: run dune build --profile web`);
    process.exit(2);
  }

// {1 Loading kanon.js as a Web Worker does}

// A worker's global scope: no node (process, require), importScripts; what
// kanon writes on its standard error (console.error) is kept in [stderr].
const stderr = [];
const worker = vm.createContext({
  console: { ...console, error: (...a) => stderr.push(a.join(" ")) },
  crypto: globalThis.crypto,
  performance,
  TextEncoder,
  TextDecoder,
  setTimeout,
  clearTimeout,
});
worker.self = worker;
worker.importScripts = (...urls) => {
  for (const url of urls)
    vm.runInContext(fs.readFileSync(url, "utf8"), worker, { filename: url });
};
let ready = false;
worker.onkanonready = () => {
  ready = true;
};
const t0 = performance.now();
vm.runInContext(`importScripts(${JSON.stringify(script)})`, worker);
const loadTime = performance.now() - t0;
const kanon = worker.kanon;
check(ready, "onkanonready is called");
check(kanon !== undefined, "globalThis.kanon is defined");
if (kanon === undefined) process.exit(1);

console.log(`kanon.js ${kanon.version}: loaded in ${loadTime.toFixed(0)} ms`);
check(typeof kanon.version === "string" && kanon.version !== "", "version");
same(kanon.root, "/sandbox", "root");
same(Array.from(kanon.backends), partBackends, "backends");
for (const f of ["bool.knl", "bool.kn"])
  same(
    kanon.builtins[f],
    fs.readFileSync(path.join(repo, "modules", f), "utf8"),
    `builtins[${f}]`,
  );

const root = kanon.root;

// {1 The virtual file system}

kanon.writeFile(`${root}/a/b/c.kn`, "fn x é");
same(kanon.readFile(`${root}/a/b/c.kn`), "fn x é", "readFile of writeFile");
same(kanon.readFile("a/b/c.kn"), "fn x é", "readFile of a relative path");
same(Array.from(kanon.listFiles(root)), [`${root}/a/b/c.kn`], "listFiles");
kanon.writeFile(`${root}/a/b/c.kn`, "replaced");
same(kanon.readFile(`${root}/a/b/c.kn`), "replaced", "writeFile replaces");
kanon.removeFile(`${root}/a/b/c.kn`);
same(kanon.readFile(`${root}/a/b/c.kn`), null, "readFile of a removed file");
same(Array.from(kanon.listFiles(root)), [], "listFiles after removeFile");
let threw = false;
try {
  kanon.removeFile(`${root}/nope`);
} catch (e) {
  threw = e instanceof Error || e?.constructor?.name === "Error";
}
check(threw, "removeFile of a missing file throws an Error");

/** Removes all the files of the root. */
function clear() {
  for (const f of kanon.listFiles(root)) kanon.removeFile(f);
}

/** Writes the files of the directory [dir] matching [re] under [to]. */
function copy(dir, to, re = /\.knl?$/) {
  for (const f of fs.readdirSync(dir))
    if (re.test(f))
      kanon.writeFile(`${to}/${f}`, fs.readFileSync(path.join(dir, f), "utf8"));
}

// {1 The command line}

/** Runs [kanon.run args] in the web runtime in [webCwd] (relative to the root),
    and compares it with the part of the native kanon on the same files in
    [cwd]: the files that `kanon ocaml` and `kanon lean` write. */
function compare(args, cwd, webCwd, what) {
  const [backend, ...files] = args;
  const text = fs
    .readdirSync(cwd)
    .filter((f) => f.endsWith(".knl"))
    .map((f) => fs.readFileSync(path.join(cwd, f), "utf8"))
    .join("\n");
  const n = (files.length > 0 && nativeParts(native, cwd, files, text)[backend]) || {
    code: 2,
    stdout: "",
    stderr: usage,
  };
  const webArgs = args.map((a, i) =>
    i > 0 && webCwd && !a.startsWith("+") ? `${webCwd}/${a}` : a,
  );
  const t = performance.now();
  const w = kanon.run(webArgs);
  const time = performance.now() - t;
  const norm = (s) => (webCwd ? s.replaceAll(`${webCwd}/`, "") : s);
  // the files of a part of Lean, in any order
  const chunks = (s) =>
    backend?.startsWith("lean-")
      ? s
          .split(/^(?=-- Generated\/\S+\.lean\n)/m)
          .map((c) => c.trimEnd())
          .sort()
      : s;
  same(
    { code: w.code, stdout: chunks(w.stdout), stderr: norm(w.stderr) },
    { code: n.code, stdout: chunks(n.stdout), stderr: n.stderr },
    `${what}: kanon.run ${args.join(" ")}`,
  );
  return time;
}

clear();
const bool = path.join(repo, "examples/bool");
kanon.writeFile(
  `${root}/lang.knl`,
  fs.readFileSync(path.join(bool, "lang.knl"), "utf8"),
);
for (const b of kanon.backends)
  compare([b, "lang.knl"], bool, "", "examples/bool");
compare([], bool, "", "usage");
compare(["ocaml"], bool, "", "usage");
compare(["lean-everything", "lang.knl"], bool, "", "unknown backend");
compare(["ocaml", "+nope"], bool, "", "unknown built-in module");
// the types of a built-in module alone (its rules need primitives that a
// language declares, so there is no kanon ocaml to compare with)
{
  const w = kanon.run(["ocaml-types", "+bool.knl"]);
  check(
    w.code === 0 && w.stdout.startsWith("(* Generated by kanon from bool.knl. Do not edit. *)"),
    "built-in module: kanon.run ocaml-types +bool.knl",
    JSON.stringify(w).slice(0, 300),
  );
}

const tiny = path.join(repo, "test/tiny.t");
copy(tiny, `${root}/tiny`);
for (const b of kanon.backends)
  compare([b, "lang.knl"], tiny, "tiny", "tiny.t");
{
  // errors in a file
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "kanon-web-"));
  for (const f of fs.readdirSync(tiny))
    fs.copyFileSync(path.join(tiny, f), path.join(dir, f));
  fs.writeFileSync(path.join(dir, "bad.kn"), "fn f (x : t) : t = y\n");
  kanon.writeFile(`${root}/tiny/bad.kn`, "fn f (x : t) : t = y\n");
  compare(["ocaml", "lang.knl", "bad.kn"], dir, "tiny", "an error");
  fs.writeFileSync(path.join(dir, "syntax.kn"), "fn f (x : t) : t =\n");
  kanon.writeFile(`${root}/tiny/syntax.kn`, "fn f (x : t) : t =\n");
  compare(["ocaml", "lang.knl", "syntax.kn"], dir, "tiny", "a syntax error");
  fs.rmSync(dir, { recursive: true });
}
{
  // a file that is missing is an error of kanon, with its path in the runtime
  const w = kanon.run(["ocaml", "missing.knl"]);
  same(
    w,
    {
      code: 1,
      stdout: "",
      stderr: `kanon: missing.knl: ${root}/missing.knl: No such file or directory\n`,
    },
    "a missing file",
  );
  // nor do arguments that are not strings
  let r;
  try {
    r = kanon.run(null);
  } catch (e) {
    r = e;
  }
  same(r.code, 2, "run(null) fails without throwing");
}

// {1 The language server}

/** The messages of the server, parsed. */
const lsp = (m) => Array.from(kanon.lsp(JSON.stringify(m))).map(JSON.parse);
const checkNow = () => Array.from(kanon.check()).map(JSON.parse);

const lspDir = path.join(repo, "test/lsp.t");
const uri = (f) => `file://${root}/${f}`;
let id = 0;
const request = (method, params) => {
  const msgs = lsp({ jsonrpc: "2.0", id: ++id, method, params });
  const r = msgs.filter((m) => m.id === id);
  same(r.length, 1, `one response to ${method}`);
  return { result: r[0]?.result, error: r[0]?.error, msgs };
};
const at = (method, f, line, character) =>
  request(`textDocument/${method}`, {
    textDocument: { uri: uri(f) },
    position: { line, character },
  });
const notify = (method, params) => lsp({ jsonrpc: "2.0", method, params });
const diagnostics = (msgs, f) =>
  msgs.filter(
    (m) =>
      m.method === "textDocument/publishDiagnostics" && m.params.uri === uri(f),
  );

clear();
copy(lspDir, root);
const imp = fs.readFileSync(path.join(lspDir, "imp.kn"), "utf8");
const fixed = imp.replace("Bool.not_ 1", "Bool.not_ a");

const init = request("initialize", {
  rootUri: `file://${root}`,
  capabilities: {},
});
check(
  init.result?.capabilities?.definitionProvider === true,
  "initialize",
  JSON.stringify(init),
);
same(notify("initialized", {}), [], "initialized");
same(
  notify("textDocument/didOpen", {
    textDocument: {
      uri: uri("imp.kn"),
      languageId: "kanon",
      version: 1,
      text: imp,
    },
  }),
  [],
  "didOpen sends nothing before the check",
);
let msgs = checkNow();
same(
  diagnostics(msgs, "imp.kn").map((m) => m.params.diagnostics),
  [
    [
      {
        range: {
          start: { line: 1, character: 31 },
          end: { line: 1, character: 32 },
        },
        severity: 1,
        source: "kanon",
        message: "type mismatch: expected t, got int",
      },
    ],
  ],
  "the type error of imp.kn",
);
same(checkNow(), [], "a check without changes sends nothing");
notify("textDocument/didChange", {
  textDocument: { uri: uri("imp.kn"), version: 2 },
  contentChanges: [{ text: fixed }],
});
msgs = checkNow();
same(
  diagnostics(msgs, "imp.kn").map((m) => m.params.diagnostics),
  [[]],
  "the type error of imp.kn is fixed",
);

// a definition in the bool module, built into kanon
let r = at("definition", "imp.kn", 1, 27);
const loc = r.result?.[0];
check(
  loc?.uri?.startsWith("file:///") && loc.uri.endsWith("/bool.kn"),
  "definition in bool.kn",
  JSON.stringify(r),
);
same(
  loc?.range,
  { start: { line: 49, character: 5 }, end: { line: 49, character: 9 } },
  "range of the definition in bool.kn",
);
const builtinPath = decodeURIComponent(loc?.uri?.slice(7) ?? "");
same(
  kanon.readFile(builtinPath),
  kanon.builtins["bool.kn"],
  `readFile of the definition (${builtinPath})`,
);
same(
  at("definition", "imp.kn", 6, 29).result,
  [
    {
      uri: uri("imp.kn"),
      range: {
        start: { line: 1, character: 3 },
        end: { line: 1, character: 6 },
      },
    },
  ],
  "definition of neg",
);
r = at("hover", "imp.kn", 1, 27);
same(
  r.result?.contents?.value,
  "```kanon\nrule not_ : Not sv\n```\n\n*bool.kn*",
  "hover of Bool.not_",
);
r = at("completion", "imp.kn", 6, 0);
const labels = (
  Array.isArray(r.result) ? r.result : (r.result?.items ?? [])
).map((i) => i.label);
for (const l of ["neg", "b_imp", "Bool.not_", "Imp", "implies", "rule"])
  check(labels.includes(l), `completion offers ${l}`, labels.join(" "));
r = request("textDocument/documentSymbol", {
  textDocument: { uri: uri("more.kn") },
});
same(r.result?.[0]?.name, "extend Imp.b_imp", "documentSymbol");
r = request("kanon/unknown", {});
same(r.error?.code, -32601, "unknown method");
same(lsp({ jsonrpc: "2.0", method: "exit" }), [], "exit is ignored");
stderr.length = 0;
same(kanon.lsp("not json").length, 0, "a message that is not JSON");
check(
  stderr.join("\n").startsWith("kanon: bad message: "),
  "a message that is not JSON is reported on the console",
  stderr.join("\n"),
);

// The same session natively: the same responses, and the same last
// diagnostics of each file
{
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "kanon-web-lsp-"));
  for (const f of fs.readdirSync(lspDir))
    if (/\.knl?$/.test(f))
      fs.copyFileSync(path.join(lspDir, f), path.join(dir, f));
  const messages = [];
  let n = 0;
  const send = (m) => messages.push(JSON.stringify(m));
  const nuri = (f) => `file://${dir}/${f}`;
  const nat = (f, line, character) => ({
    textDocument: { uri: nuri(f) },
    position: { line, character },
  });
  // the session of the web runtime, again
  clear();
  copy(lspDir, root);
  const web = [];
  const wsend = (m) => web.push(...Array.from(kanon.lsp(JSON.stringify(m))));
  const both = (m, nm) => {
    send(nm ?? m);
    wsend(m);
  };
  const req = (method, f, line, character) => {
    n++;
    send({
      jsonrpc: "2.0",
      id: n,
      method: `textDocument/${method}`,
      params: nat(f, line, character),
    });
    wsend({
      jsonrpc: "2.0",
      id: n,
      method: `textDocument/${method}`,
      params: { textDocument: { uri: uri(f) }, position: { line, character } },
    });
  };
  both(
    {
      jsonrpc: "2.0",
      id: 0,
      method: "initialize",
      params: { rootUri: `file://${root}`, capabilities: {} },
    },
    {
      jsonrpc: "2.0",
      id: 0,
      method: "initialize",
      params: { rootUri: `file://${dir}`, capabilities: {} },
    },
  );
  const open = (f, text) => ({
    jsonrpc: "2.0",
    method: "textDocument/didOpen",
    params: { textDocument: { uri: f, languageId: "kanon", version: 1, text } },
  });
  both(
    open(uri("more.kn"), fs.readFileSync(path.join(lspDir, "more.kn"), "utf8")),
    open(
      nuri("more.kn"),
      fs.readFileSync(path.join(lspDir, "more.kn"), "utf8"),
    ),
  );
  req("hover", "more.kn", 0, 30);
  both(open(uri("imp.kn"), imp), open(nuri("imp.kn"), imp));
  req("hover", "imp.kn", 6, 29);
  const change = (f, text) => ({
    jsonrpc: "2.0",
    method: "textDocument/didChange",
    params: {
      textDocument: { uri: f, version: 2 },
      contentChanges: [{ text }],
    },
  });
  both(change(uri("imp.kn"), fixed), change(nuri("imp.kn"), fixed));
  req("definition", "imp.kn", 1, 27);
  req("hover", "imp.kn", 1, 27);
  req("definition", "imp.kn", 3, 14);
  req("definition", "more.kn", 0, 30);
  req("completion", "imp.kn", 6, 0);
  both(
    change(uri("imp.kn"), fixed.replace("Bool.not_ a", "Bool.not_ a in")),
    change(nuri("imp.kn"), fixed.replace("Bool.not_ a", "Bool.not_ a in")),
  );
  req("hover", "imp.kn", 3, 14);
  n++;
  both(
    {
      jsonrpc: "2.0",
      id: n,
      method: "textDocument/documentSymbol",
      params: { textDocument: { uri: uri("more.kn") } },
    },
    {
      jsonrpc: "2.0",
      id: n,
      method: "textDocument/documentSymbol",
      params: { textDocument: { uri: nuri("more.kn") } },
    },
  );
  n++;
  both({
    jsonrpc: "2.0",
    id: n,
    method: "workspace/symbol",
    params: { query: "IMP" },
  });
  web.push(...Array.from(kanon.check()));
  send({ jsonrpc: "2.0", id: n + 1, method: "shutdown" });
  send({ jsonrpc: "2.0", method: "exit" });
  const input = messages
    .map((m) => `Content-Length: ${Buffer.byteLength(m)}\r\n\r\n${m}`)
    .join("");
  const p = spawnSync(native, ["lsp"], { input, encoding: "utf8" });
  same(p.status, 0, "native kanon lsp exits");
  const nativeMsgs = p.stdout
    .split(/Content-Length: \d+\r\n\r\n/)
    .filter((s) => s !== "")
    .map((s) => s.replaceAll(`file://${dir}/`, `file://${root}/`));
  const norm = (s) =>
    s.replace(/file:\/\/[^"]*\/kanon-modules-[0-9a-f]*\//g, "BUILTIN/");
  const byId = (l) =>
    Object.fromEntries(
      l
        .map((s) => JSON.parse(norm(s)))
        .filter((m) => "id" in m)
        .map((m) => [m.id, m]),
    );
  const lastDiags = (l) => {
    const d = {};
    for (const m of l.map((s) => JSON.parse(norm(s))))
      if (m.method === "textDocument/publishDiagnostics")
        d[m.params.uri] = m.params.diagnostics;
    return d;
  };
  const nIds = byId(nativeMsgs);
  delete nIds[n + 1];
  same(byId(web), nIds, "the responses of the session are those of kanon lsp");
  same(
    lastDiags(web),
    lastDiags(nativeMsgs),
    "the last diagnostics of the session are those of kanon lsp",
  );
  fs.rmSync(dir, { recursive: true });
}

// {1 Soteria's Bv_values}

if (fs.existsSync(path.join(soteria, "lib/bv_values/rules/lang.knl"))) {
  clear();
  const rules = "soteria/lib/bv_values/rules";
  copy(path.join(soteria, "lib/bv_values/rules"), `${root}/${rules}`);
  copy(path.join(soteria, "kanon/modules"), `${root}/soteria/kanon/modules`);
  const cwd = path.join(soteria, "lib/bv_values/rules");
  const runTimes = {};
  for (const b of kanon.backends)
    runTimes[b] = compare([b, "lang.knl"], cwd, rules, "Bv_values");
  // the check of the language server: the first, then the median of 5
  const lang = `${root}/${rules}/lang.knl`;
  const text = kanon.readFile(lang);
  lsp({
    jsonrpc: "2.0",
    id: 1000,
    method: "initialize",
    params: { rootUri: `file://${root}`, capabilities: {} },
  });
  lsp({
    jsonrpc: "2.0",
    method: "textDocument/didOpen",
    params: {
      textDocument: {
        uri: `file://${lang}`,
        languageId: "kanon",
        version: 1,
        text,
      },
    },
  });
  let t = performance.now();
  msgs = checkNow();
  const first = performance.now() - t;
  const errors = msgs.flatMap((m) => m.params?.diagnostics ?? []);
  same(errors, [], "Bv_values checks without errors");
  const symbols = request("textDocument/documentSymbol", {
    textDocument: { uri: `file://${root}/${rules}/bitvec.kn` },
  }).result;
  check(
    Array.isArray(symbols) && symbols.length > 50,
    "Bv_values: the symbols of bitvec.kn",
    JSON.stringify(symbols)?.slice(0, 200),
  );
  const times = [];
  for (let i = 0; i < 5; i++) {
    lsp({
      jsonrpc: "2.0",
      method: "textDocument/didChange",
      params: {
        textDocument: { uri: `file://${lang}`, version: i + 2 },
        contentChanges: [{ text: text + " ".repeat(i + 1) }],
      },
    });
    t = performance.now();
    checkNow();
    times.push(performance.now() - t);
  }
  times.sort((a, b) => a - b);
  t = performance.now();
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), "kanon-web-"));
  spawnSync(native, ["ocaml", outDir, "lang.knl"], { cwd });
  fs.rmSync(outDir, { recursive: true });
  const nativeTime = performance.now() - t;
  console.log(
    `Bv_values: check ${first.toFixed(0)} ms (first), ${times[2].toFixed(0)} ms (median of 5); ` +
      `kanon.run ocaml ${runTimes.ocaml.toFixed(0)} ms, lean-soundness ${runTimes["lean-soundness"].toFixed(0)} ms ` +
      `(native kanon ocaml, with its start: ${nativeTime.toFixed(0)} ms)`,
  );
} else
  console.log(`Bv_values: skipped, no soteria at ${soteria} (set SOTERIA)`);

console.log(`${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
