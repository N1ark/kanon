// A mock of the web runtime of Kanon (dune build @web --profile web: _build/default/web/dist/
// kanon.js), for developing the site without it: a classic script for a Web
// Worker with the same API, globalThis.kanon. The site's build serves it at
// kanon/kanon.js instead of the real runtime when KANON_MOCK=1 (see
// vite.config.ts), with KANON_MOCK_DATA defined before it:
// { builtins: { "bool.knl": ..., "bool.kn": ... }, fixtures: mock/fixtures.json }.
//
// `run` answers with the canned outputs of mock/fixtures.json (computed by a
// native kanon, see scripts/mock-fixtures.mjs) when the files are those of an
// example, and otherwise with those of the closest example, marked stale. The
// language server is a rough imitation: it finds definitions by their
// keywords, and reports unbalanced brackets, missing modules and unknown nodes
// in specs.

/* global KANON_MOCK_DATA */
(function () {
  "use strict";
  const data = typeof KANON_MOCK_DATA !== "undefined" ? KANON_MOCK_DATA : { builtins: {}, fixtures: { backends: [], runs: [] } };
  const ROOT = "/sandbox";
  const BUILTIN_DIR = "/tmp/kanon-modules-mock";
  const fs = new Map();
  for (const [name, text] of Object.entries(data.builtins)) fs.set(`${BUILTIN_DIR}/${name}`, text);

  const dirname = (p) => p.slice(0, p.lastIndexOf("/")) || "/";
  const basename = (p) => p.slice(p.lastIndexOf("/") + 1);
  const uriToPath = (u) => decodeURIComponent(u.replace(/^file:\/\//, ""));
  const pathToUri = (p) => "file://" + p;

  function listFiles(dir) {
    const d = dir.replace(/\/$/, "");
    return [...fs.keys()].filter((p) => dirname(p) === d).map(basename).sort();
  }

  // ---------------------------------------------------------------- the index

  const KEYWORDS = ["use", "type", "of", "node", "infix", "prefix", "constant", "extend", "before",
    "rule", "fn", "prim", "oracle", "let", "in", "match", "with", "if", "then", "else", "when", "as",
    "not", "true", "false", "type_of"];

  // The definitions of a file: { name, kind, line, col, header, doc, container }
  function definitions(path, text) {
    const defs = [];
    const lines = text.split("\n");
    let fun = null; // the rule function whose cases follow
    let inType = false;
    const docAbove = (i) => {
      let j = i - 1;
      if (j < 0 || !/\*\)\s*$/.test(lines[j])) return "";
      const acc = [];
      while (j >= 0) {
        acc.unshift(lines[j]);
        if (/^\s*\(\*/.test(lines[j])) break;
        j--;
      }
      return acc.join("\n").replace(/^\s*\(\*+\s?/, "").replace(/\s*\*\)\s*$/, "").replace(/\n\s+/g, "\n").trim();
    };
    lines.forEach((line, i) => {
      let m;
      const def = (name, kind, col, header) =>
        defs.push({ path, name, kind, line: i, col, header, doc: docAbove(i), container: null });
      if ((m = /^(\s*)(rule|fn|prim|oracle)\s+([a-z_][\w']*)/.exec(line))) {
        def(m[3], m[2] === "rule" ? "rule" : m[2] === "fn" ? "fn" : "prim", line.indexOf(m[3], m[1].length + m[2].length), line.replace(/\s*=.*$/, "").trim());
        fun = m[2] === "rule" ? m[3] : null;
        inType = false;
      } else if ((m = /^\s*extend\s+rule\s+([a-z_][\w']*)/.exec(line))) {
        fun = m[1];
        inType = false;
      } else if ((m = /^\s*node\s+([A-Z][\w']*)/.exec(line))) {
        def(m[1], "node", line.indexOf(m[1]), line.trim());
        inType = false;
      } else if ((m = /^\s*type\s+([a-z_][\w']*)/.exec(line))) {
        def(m[1], "type", line.indexOf(m[1], line.indexOf("type") + 4), line.replace(/\s*=.*$/, "").trim());
        inType = /=\s*$/.test(line) || /=\s*\|?\s*[A-Z]/.test(line);
        for (const c of line.replace(/^[^=]*=?/, "").matchAll(/\|?\s*([A-Z][\w']*)/g))
          if (/=/.test(line)) def(c[1], "constructor", line.indexOf(c[1]), `${c[1]} (of type ${m[1]})`);
      } else if ((m = /^\s*(infix|prefix)\s+"([^"]+)"/.exec(line))) {
        def(m[2], "operator", line.indexOf('"') + 1, line.trim());
      } else if (inType && (m = /^\s*\|\s*([A-Z][\w']*)/.exec(line))) {
        def(m[1], "constructor", line.indexOf(m[1]), line.trim().replace(/^\|\s*/, ""));
      } else if (fun && (m = /^(\s*)\|\s*([a-z_][\w']*)\s*:/.exec(line))) {
        defs.push({ path, name: m[2], kind: "case", line: i, col: line.indexOf(m[2]), header: `rule ${fun} =\n  ${line.trim()}`, doc: "", container: fun });
      } else if (/^\S/.test(line) && !/^\s*\(\*/.test(line)) {
        inType = false;
        if (!/^\s*\|/.test(line)) fun = /^\s*extend/.test(line) ? fun : null;
      }
    });
    return defs;
  }

  function workspaceFiles() {
    return [...fs.keys()].filter((p) => dirname(p) === ROOT && /\.knl?$/.test(p));
  }

  function allDefinitions() {
    const files = [...workspaceFiles(), ...[...fs.keys()].filter((p) => dirname(p) === BUILTIN_DIR)];
    return files.flatMap((p) => definitions(p, fs.get(p)));
  }

  function wordAt(text, line, character) {
    const l = text.split("\n")[line] ?? "";
    let s = character;
    let e = character;
    while (s > 0 && /[\w']/.test(l[s - 1])) s--;
    while (e < l.length && /[\w']/.test(l[e])) e++;
    if (s === e) return null;
    return { word: l.slice(s, e), line, start: s, end: e };
  }

  const range = (line, s, e) => ({ start: { line, character: s }, end: { line, character: e } });

  function findDefinition(word, path, line) {
    const defs = allDefinitions().filter((d) => d.name === word);
    if (defs.length === 0) return null;
    // a case label: the one of the rule function around
    return defs.find((d) => d.kind !== "case") ?? defs.find((d) => d.path === path && d.line <= line) ?? defs[0];
  }

  // ---------------------------------------------------------- diagnostics

  function bracketErrors(text) {
    const out = [];
    const stack = [];
    const pairs = { ")": "(", "]": "[", "}": "{" };
    const lines = text.split("\n");
    let depth = 0; // comments nest
    let str = false;
    for (let i = 0; i < lines.length; i++) {
      const l = lines[i];
      for (let j = 0; j < l.length; j++) {
        const c = l[j];
        if (depth > 0) {
          if (c === "(" && l[j + 1] === "*") { depth++; j++; } else if (c === "*" && l[j + 1] === ")") { depth--; j++; }
          continue;
        }
        if (str) { if (c === "\\") j++; else if (c === '"') str = false; continue; }
        if (c === '"') { str = true; continue; }
        if (c === "(" && l[j + 1] === "*") { depth = 1; j++; continue; }
        if ("([{".includes(c)) stack.push({ c, line: i, col: j });
        else if (")]}".includes(c)) {
          const top = stack.pop();
          if (!top || top.c !== pairs[c]) { out.push({ line: i, col: j, message: "syntax error" }); return out; }
        }
      }
    }
    if (depth > 0) out.push({ line: lines.length - 1, col: 0, message: "unterminated comment" });
    for (const t of stack.slice(0, 1)) out.push({ line: t.line, col: t.col, message: "syntax error: unclosed bracket" });
    return out;
  }

  function diagnosticsOf(path) {
    const text = fs.get(path) ?? "";
    const diags = [];
    for (const e of bracketErrors(text)) diags.push({ range: range(e.line, e.col, e.col + 1), severity: 1, source: "kanon", message: e.message });
    const nodes = new Set(allDefinitions().filter((d) => d.kind === "node" || d.kind === "constructor").map((d) => d.name));
    text.split("\n").forEach((l, i) => {
      let m;
      if ((m = /^\s*use\s+"([^"]+)"/.exec(l))) {
        const base = `${dirname(path)}/${m[1]}`;
        if (!fs.has(base + ".knl") && !fs.has(base + ".kn"))
          diags.push({ range: range(i, l.indexOf("use"), l.trimEnd().length), severity: 1, source: "kanon", message: `use "${m[1]}": no ${base}.knl or ${base}.kn` });
      }
      if ((m = /^\s*rule\s+[a-z_][\w']*[^:]*:\s*([A-Z][\w']*)/.exec(l)) && !nodes.has(m[1])) {
        const s = l.indexOf(m[1], l.indexOf(":"));
        diags.push({ range: range(i, s, s + m[1].length), severity: 1, source: "kanon", message: `unknown node ${m[1]}` });
      }
    });
    return diags;
  }

  let pending = true;
  function check() {
    if (!pending) return [];
    pending = false;
    return workspaceFiles().map((p) =>
      JSON.stringify({ jsonrpc: "2.0", method: "textDocument/publishDiagnostics", params: { uri: pathToUri(p), diagnostics: diagnosticsOf(p) } }));
  }

  // ---------------------------------------------------------- the server

  const SYMBOL = { rule: 12, fn: 12, prim: 12, node: 9, type: 5, constructor: 9, operator: 25, case: 22 };
  const COMPLETION = { rule: 3, fn: 3, prim: 3, node: 4, type: 7, constructor: 4, operator: 24, case: 20 };

  function occurrences(word) {
    const re = new RegExp(`(?<![\\w'])${word.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w'])`, "g");
    const locs = [];
    for (const p of workspaceFiles())
      fs.get(p).split("\n").forEach((l, i) => {
        for (const m of l.matchAll(re)) locs.push({ uri: pathToUri(p), range: range(i, m.index, m.index + word.length) });
      });
    return locs;
  }

  function handle(msg) {
    const { id, method, params } = msg;
    const reply = (result) => [JSON.stringify({ jsonrpc: "2.0", id, result })];
    const textOf = (p) => fs.get(uriToPath(p.textDocument.uri)) ?? "";
    switch (method) {
      case "initialize":
        return reply({
          capabilities: {
            textDocumentSync: { openClose: true, change: 1, save: { includeText: false } },
            definitionProvider: true, hoverProvider: true, completionProvider: {},
            workspaceSymbolProvider: true, documentSymbolProvider: true,
            referencesProvider: true, documentHighlightProvider: true, renameProvider: true,
          },
          serverInfo: { name: "kanon (mock)" },
        });
      case "initialized": case "exit": case "$/cancelRequest": return [];
      case "shutdown": return reply(null);
      case "textDocument/didOpen":
        fs.set(uriToPath(params.textDocument.uri), params.textDocument.text); pending = true; return [];
      case "textDocument/didChange":
        fs.set(uriToPath(params.textDocument.uri), params.contentChanges.at(-1).text); pending = true; return [];
      case "textDocument/didClose": case "textDocument/didSave": pending = true; return [];
      case "workspace/didChangeWatchedFiles": pending = true; return [];
      case "textDocument/hover": {
        const path = uriToPath(params.textDocument.uri);
        const w = wordAt(textOf(params), params.position.line, params.position.character);
        const d = w && findDefinition(w.word, path, w.line);
        if (!d) return reply(null);
        const value = "```kanon\n" + d.header + "\n```\n\n" + (d.doc ? d.doc + "\n\n" : "") + `*${basename(d.path)}*`;
        return reply({ contents: { kind: "markdown", value }, range: range(w.line, w.start, w.end) });
      }
      case "textDocument/definition": {
        const path = uriToPath(params.textDocument.uri);
        const w = wordAt(textOf(params), params.position.line, params.position.character);
        const d = w && findDefinition(w.word, path, w.line);
        return reply(d ? [{ uri: pathToUri(d.path), range: range(d.line, d.col, d.col + d.name.length) }] : null);
      }
      case "textDocument/completion": {
        const seen = new Set();
        const items = [];
        for (const d of allDefinitions()) {
          if (d.kind === "case" || seen.has(d.name)) continue;
          seen.add(d.name);
          items.push({ label: d.name, kind: COMPLETION[d.kind], detail: d.header.split("\n")[0] });
        }
        for (const k of KEYWORDS) items.push({ label: k, kind: 14 });
        return reply(items);
      }
      case "textDocument/documentSymbol": {
        const path = uriToPath(params.textDocument.uri);
        const defs = definitions(path, fs.get(path) ?? "");
        const syms = [];
        for (const d of defs) {
          const sym = { name: d.name, detail: d.header.split("\n").at(-1), kind: SYMBOL[d.kind], range: range(d.line, 0, (fs.get(path).split("\n")[d.line] ?? "").length), selectionRange: range(d.line, d.col, d.col + d.name.length), children: [] };
          const parent = d.kind === "case" ? [...syms].reverse().find((s) => s.name === d.container || s.name === `extend ${d.container}`) : null;
          if (parent) parent.children.push(sym); else if (d.kind !== "case") syms.push(sym);
        }
        return reply(syms);
      }
      case "workspace/symbol": {
        const q = (params.query ?? "").toLowerCase();
        return reply(allDefinitions().filter((d) => dirname(d.path) === ROOT && d.name.toLowerCase().includes(q)).map((d) => ({
          name: d.container ? `${d.container}/${d.name}` : d.name, kind: SYMBOL[d.kind],
          location: { uri: pathToUri(d.path), range: range(d.line, d.col, d.col + d.name.length) },
          ...(d.container ? { containerName: d.container } : {}),
        })));
      }
      case "textDocument/references": {
        const w = wordAt(textOf(params), params.position.line, params.position.character);
        return reply(w ? occurrences(w.word) : []);
      }
      case "textDocument/documentHighlight": {
        const w = wordAt(textOf(params), params.position.line, params.position.character);
        if (!w || KEYWORDS.includes(w.word)) return reply([]);
        return reply(occurrences(w.word).filter((l) => l.uri === params.textDocument.uri).map((l) => ({ range: l.range, kind: 1 })));
      }
      case "textDocument/rename": {
        const w = wordAt(textOf(params), params.position.line, params.position.character);
        if (!w) return reply(null);
        const changes = {};
        for (const l of occurrences(w.word)) (changes[l.uri] ??= []).push({ range: l.range, newText: params.newName });
        return reply({ changes });
      }
      default:
        if (id === undefined) return [];
        return [JSON.stringify({ jsonrpc: "2.0", id, error: { code: -32601, message: `unknown method ${method}` } })];
    }
  }

  // ---------------------------------------------------------- kanon run

  const backends = data.fixtures.backends;
  const USAGE = `usage: kanon (${backends.join(" | ")} | lean-all) FILE...\n       kanon lsp\n`;

  function run(args) {
    const [backend, file] = args;
    if (!backends.includes(backend) || !file) return { code: 2, stdout: "", stderr: USAGE };
    if (!fs.has(file)) return { code: 1, stdout: "", stderr: `kanon: ${file}: no such file\n` };
    const dir = dirname(file);
    for (const p of [...fs.keys()].filter((p) => dirname(p) === dir && /\.knl?$/.test(p))) {
      const d = diagnosticsOf(p)[0];
      if (d) return { code: 1, stdout: "", stderr: `${p}:${d.range.start.line + 1}:${d.range.start.character}: ${d.message}\n` };
    }
    const files = Object.fromEntries([...fs.keys()].filter((p) => dirname(p) === dir && /\.knl?$/.test(p)).map((p) => [basename(p), fs.get(p)]));
    const same = (a, b) => Object.keys(a).length === Object.keys(b).length && Object.keys(a).every((k) => a[k] === b[k]);
    const runs = data.fixtures.runs.filter((r) => r.root === basename(file));
    const exact = runs.find((r) => same(r.files, files));
    if (exact) return exact.outputs[backend];
    // the closest example: the most files in common, then the most equal ones
    const score = (r) => Object.keys(files).filter((k) => k in r.files).length * 1000 + Object.keys(files).filter((k) => r.files[k] === files[k]).length;
    const best = runs.sort((a, b) => score(b) - score(a))[0];
    if (!best) return { code: 1, stdout: "", stderr: "mock runtime: no canned output\n" };
    const out = best.outputs[backend];
    const note = backend.startsWith("lean") ? "-- " : "(* ";
    const end = backend.startsWith("lean") ? "" : " *)";
    return { ...out, stdout: out.stdout && `${note}Mock runtime: canned output of the example "${best.example}", not of these files.${end}\n\n${out.stdout}` };
  }

  globalThis.kanon = {
    version: "mock",
    root: ROOT,
    backends,
    builtins: data.builtins,
    writeFile(path, contents) { fs.set(path, contents); pending = true; },
    removeFile(path) { fs.delete(path); pending = true; },
    readFile(path) { return fs.has(path) ? fs.get(path) : null; },
    listFiles,
    lsp(message) { return handle(JSON.parse(message)); },
    check,
    run,
  };
  // initialisation may be asynchronous: the real runtime loads its assets first
  setTimeout(() => { if (typeof globalThis.onkanonready === "function") globalThis.onkanonready(); }, 0);
})();
