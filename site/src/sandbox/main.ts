// The sandbox: a multi-file editor of a Kanon language, with the language
// server of the runtime (diagnostics, hovers, completion, definitions, and
// references, rename and highlights when the server provides them), the code
// that the backends generate, and the files saved in localStorage or shared in
// the URL.

import "../styles/base.css";
import "./sandbox.css";
import { setDiagnostics, type Diagnostic as CmDiagnostic } from "@codemirror/lint";
import { EditorState } from "@codemirror/state";
import { EditorView } from "@codemirror/view";
import { exampleById, examples, roots } from "../examples";
import { loadKanonSyntax } from "../highlight/kanon";
import { KanonRuntime } from "../runtime/client";
import { LspClient, locations, type Diagnostic, type Location, type TextEdit } from "../runtime/lsp";
import { initTheme } from "../theme";
import { debounce, el } from "../util";
import { kanonExtensions, toOffsets, toPosition, type LspHost } from "./editor";
import { Outputs } from "./outputs";
import * as persist from "./persist";

initTheme();

interface FileEntry {
  name: string;
  state: EditorState;
  /** A read-only file of a built-in module, at this path of the runtime. */
  builtinPath?: string;
  /** Changed since it was last sent to the runtime. */
  dirty: boolean;
  /** Opened in the language server. */
  opened: boolean;
}

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
const status = $<HTMLSpanElement>("status");
const tabs = $<HTMLDivElement>("tabs");
const outline = $<HTMLSelectElement>("outline");
const problems = $<HTMLUListElement>("problems");
const references = $<HTMLUListElement>("references");

const syntax = await loadKanonSyntax();
let runtime: KanonRuntime | null = null;
let lsp: LspClient | null = null;
let files: FileEntry[] = [];
let active: FileEntry;
const diagnostics = new Map<string, Diagnostic[]>();

const root = () => runtime?.info.root ?? "/sandbox";
const pathOf = (f: FileEntry) => f.builtinPath ?? `${root()}/${f.name}`;
const uriOf = (f: FileEntry) => "file://" + pathOf(f);
const uriToPath = (uri: string) => decodeURIComponent(uri.replace(/^file:\/\//, ""));
const workspace = () => files.filter((f) => !f.builtinPath);
const stateOf = (f: FileEntry) => (f === active ? view.state : f.state);
const textOf = (f: FileEntry) => stateOf(f).doc.toString();
const fileByUri = (uri: string) => files.find((f) => uriOf(f) === uri);

function toast(message: string) {
  const t = $<HTMLDivElement>("toast");
  t.textContent = message;
  t.hidden = false;
  clearTimeout((toast as any).timer);
  (toast as any).timer = setTimeout(() => (t.hidden = true), 2800);
}

// ------------------------------------------------------------------ editor

function hostFor(f: FileEntry): LspHost {
  return {
    lsp: () => lsp,
    uri: () => uriOf(f),
    flush,
    syntax,
    goToDefinition: (view, pos) => goToDefinition(view, pos),
    findReferences: (view, pos) => findReferences(view, pos),
    rename: (view, pos) => rename(f, view, pos),
  };
}

function makeState(f: FileEntry, doc: string) {
  return EditorState.create({
    doc,
    extensions: kanonExtensions(hostFor(f), !!f.builtinPath, (u) => {
      if (u.docChanged) edited(f);
    }),
  });
}

function newEntry(name: string, text: string, builtinPath?: string): FileEntry {
  const f: FileEntry = { name, builtinPath, dirty: true, opened: false, state: undefined as unknown as EditorState };
  f.state = makeState(f, text);
  return f;
}

const view = new EditorView({ parent: $("editor") });
// for the console, and the tests of scripts/screenshots.mjs
(window as any).sandbox = { view };

function switchTo(f: FileEntry) {
  if (f !== active) {
    if (active) active.state = view.state;
    active = f;
    view.setState(f.state);
  }
  renderTabs();
  refreshOutline();
  saveLater();
}

// ------------------------------------------------------------------ sync

const syncLater = debounce(async () => {
  await flush();
  if (!lsp) return;
  await lsp.check();
  refreshOutline();
  outputs.changedFiles();
}, 200);

let flushing: Promise<void> = Promise.resolve();

/** Sends the changed files to the runtime and to the language server. */
function flush(): Promise<void> {
  flushing = flushing.then(async () => {
    if (!runtime || !lsp) return;
    for (const f of workspace()) {
      if (!f.dirty) continue;
      f.dirty = false;
      const text = textOf(f);
      await runtime.writeFile(pathOf(f), text);
      if (f.opened) await lsp.didChange(uriOf(f), text);
      else {
        f.opened = true;
        await lsp.didOpen(uriOf(f), text);
      }
    }
  });
  return flushing;
}

function edited(f: FileEntry) {
  if (f.builtinPath) return;
  f.dirty = true;
  syncLater();
  saveLater();
}

async function closeFile(f: FileEntry) {
  files = files.filter((g) => g !== f);
  const uri = uriOf(f);
  diagnostics.delete(uri);
  if (!f.builtinPath && runtime && lsp) {
    await flush();
    await runtime.removeFile(pathOf(f));
    if (f.opened) await lsp.didClose(uri);
    // the other files may depend on it
    workspace().forEach((g) => (g.dirty = true));
  }
  renderProblems();
}

// ------------------------------------------------------------------ diagnostics

function applyDiagnostics(f: FileEntry) {
  const state = stateOf(f);
  const doc = state.doc;
  const cm: CmDiagnostic[] = (diagnostics.get(uriOf(f)) ?? []).map((d) => {
    let { from, to } = toOffsets(doc, d.range);
    if (to === from) to = Math.min(doc.length, from + 1);
    if (to === from && from > 0) from--;
    return {
      from,
      to,
      severity: d.severity === 2 ? "warning" : d.severity === 3 || d.severity === 4 ? "info" : "error",
      message: d.message,
      source: d.source,
    };
  });
  if (f === active) view.dispatch(setDiagnostics(state, cm));
  else f.state = state.update(setDiagnostics(state, cm)).state;
}

function renderProblems() {
  const items: HTMLElement[] = [];
  for (const f of files) {
    for (const d of diagnostics.get(uriOf(f)) ?? []) {
      const sev = d.severity === 2 ? "warning" : d.severity === 3 || d.severity === 4 ? "info" : "error";
      const b = el(
        "button",
        { type: "button", class: `item ${sev}` },
        el("span", { class: "sev", "aria-label": sev }, sev === "error" ? "✕" : sev === "warning" ? "!" : "i"),
        el("span", { class: "loc" }, `${f.name}:${d.range.start.line + 1}:${d.range.start.character + 1}`),
        el("span", { class: "msg" }, d.message),
      );
      b.addEventListener("click", () => openLocation({ uri: uriOf(f), range: d.range }));
      items.push(el("li", {}, b));
    }
  }
  if (!items.length) items.push(el("li", { class: "empty" }, lsp ? "No problems." : "Starting the language server…"));
  problems.replaceChildren(...items);
  const n = [...diagnostics.values()].reduce((a, d) => a + d.length, 0);
  $("problems-count").textContent = String(n);
  $("problems-count").classList.toggle("has-errors", n > 0);
  renderTabs();
}

function showPanel(which: "problems" | "references") {
  $("problems-tab").setAttribute("aria-selected", String(which === "problems"));
  $("references-tab").setAttribute("aria-selected", String(which === "references"));
  problems.hidden = which !== "problems";
  references.hidden = which !== "references";
}
$("problems-tab").addEventListener("click", () => showPanel("problems"));
$("references-tab").addEventListener("click", () => showPanel("references"));

// ------------------------------------------------------------------ navigation

async function openLocation(loc: Location) {
  const path = uriToPath(loc.uri);
  let f = files.find((g) => pathOf(g) === path);
  if (!f) {
    // a file of a built-in module: read-only
    if (!runtime) return;
    const name = path.slice(path.lastIndexOf("/") + 1);
    const text = (await runtime.readFile(path)) ?? runtime.info.builtins[name];
    if (text === undefined) {
      toast(`Cannot open ${path}`);
      return;
    }
    f = newEntry(name, text, path);
    files.push(f);
  }
  switchTo(f);
  const { from } = toOffsets(view.state.doc, loc.range);
  view.dispatch({ selection: { anchor: from }, effects: EditorView.scrollIntoView(from, { y: "center" }) });
  view.focus();
}

async function goToDefinition(v: EditorView, pos: number) {
  if (!lsp?.has("definitionProvider")) return;
  const f = files.find((g) => stateOf(g) === v.state) ?? active;
  await flush();
  const r = await lsp.request("textDocument/definition", {
    textDocument: { uri: uriOf(f) },
    position: toPosition(v.state.doc, pos),
  });
  const locs = locations(r);
  if (locs.length) openLocation(locs[0]);
  else toast("No definition found");
}

async function findReferences(v: EditorView, pos: number) {
  if (!lsp?.has("referencesProvider")) return;
  await flush();
  const r: Location[] | null = await lsp.request("textDocument/references", {
    textDocument: { uri: uriOf(active) },
    position: toPosition(v.state.doc, pos),
    context: { includeDeclaration: true },
  });
  const items = (r ?? []).map((loc) => {
    const f = fileByUri(loc.uri);
    const name = f?.name ?? uriToPath(loc.uri).split("/").pop()!;
    const lineText = f ? stateOf(f).doc.line(loc.range.start.line + 1).text.trim() : "";
    const b = el(
      "button",
      { type: "button", class: "item" },
      el("span", { class: "loc" }, `${name}:${loc.range.start.line + 1}:${loc.range.start.character + 1}`),
      el("span", { class: "msg code-line" }, lineText),
    );
    b.addEventListener("click", () => openLocation(loc));
    return el("li", {}, b);
  });
  if (!items.length) items.push(el("li", { class: "empty" }, "No references."));
  references.replaceChildren(...items);
  $("references-count").textContent = String(r?.length ?? 0);
  showPanel("references");
}

async function rename(f: FileEntry, v: EditorView, pos: number) {
  if (!lsp?.has("renameProvider") || f.builtinPath) return;
  const word = v.state.wordAt(pos);
  const old = word ? v.state.sliceDoc(word.from, word.to) : "";
  const name = prompt(`Rename ${old} to`, old);
  if (!name || name === old) return;
  await flush();
  let edit: any;
  try {
    edit = await lsp.request("textDocument/rename", {
      textDocument: { uri: uriOf(f) },
      position: toPosition(v.state.doc, pos),
      newName: name,
    });
  } catch (e) {
    toast((e as Error).message);
    return;
  }
  if (!edit) return toast("Nothing to rename here");
  const byUri: [string, TextEdit[]][] = edit.documentChanges
    ? edit.documentChanges.filter((c: any) => c.textDocument).map((c: any) => [c.textDocument.uri, c.edits])
    : Object.entries(edit.changes ?? {});
  for (const [uri, edits] of byUri) {
    const g = fileByUri(uri);
    if (!g || g.builtinPath) continue;
    const state = stateOf(g);
    const changes = edits.map((e) => ({ ...toOffsets(state.doc, e.range), insert: e.newText }));
    if (g === active) view.dispatch({ changes });
    else {
      g.state = state.update({ changes }).state;
      edited(g);
    }
  }
}

// ------------------------------------------------------------------ outline

const refreshOutline = debounce(async () => {
  const f = active;
  if (!lsp?.has("documentSymbolProvider")) return;
  await flush();
  const r: any[] | null = await lsp.request("textDocument/documentSymbol", { textDocument: { uri: uriOf(f) } }).catch(() => null);
  if (f !== active) return;
  const options = [el("option", { value: "" }, `Outline of ${f.name}`)];
  const ranges: Location["range"][] = [];
  const add = (s: any, depth: number) => {
    ranges.push(s.selectionRange ?? s.range ?? s.location.range);
    options.push(el("option", { value: String(ranges.length - 1) }, "  ".repeat(depth) + s.name));
    for (const c of s.children ?? []) add(c, depth + 1);
  };
  for (const s of r ?? []) add(s, 0);
  outline.replaceChildren(...options);
  outline.disabled = ranges.length === 0;
  (outline as any).ranges = ranges;
}, 300);

outline.addEventListener("change", () => {
  const range = (outline as any).ranges?.[Number(outline.value)];
  outline.value = "";
  if (range) openLocation({ uri: uriOf(active), range });
});

// ------------------------------------------------------------------ tabs

function renderTabs() {
  const errors = (f: FileEntry) => (diagnostics.get(uriOf(f)) ?? []).filter((d) => (d.severity ?? 1) === 1).length;
  tabs.replaceChildren(
    ...files.map((f) => {
      const n = errors(f);
      const label = el("span", { class: "name" }, f.name);
      const tab = el(
        "div",
        {
          class: "tab" + (f.builtinPath ? " builtin" : "") + (n ? " has-errors" : ""),
          role: "tab",
          tabindex: f === active ? "0" : "-1",
          "aria-selected": String(f === active),
          title: f.builtinPath ? `${f.name}: built-in module (read-only)` : `${f.name} (double-click to rename)`,
        },
        label,
      );
      if (f.builtinPath) label.prepend(el("span", { class: "lock", "aria-hidden": "true" }, "🔒"));
      if (n) tab.append(el("span", { class: "errors", "aria-label": `${n} errors` }, String(n)));
      const close = el(
        "button",
        { type: "button", class: "close", "aria-label": f.builtinPath ? `Close ${f.name}` : `Delete ${f.name}`, title: f.builtinPath ? "Close" : "Delete" },
        "×",
      );
      close.addEventListener("click", async (e) => {
        e.stopPropagation();
        if (!f.builtinPath) {
          if (workspace().length === 1) return toast("A language needs at least one file");
          if (!confirm(`Delete ${f.name}?`)) return;
        }
        const i = files.indexOf(f);
        await closeFile(f);
        if (f === active) {
          active = undefined as unknown as FileEntry;
          switchTo(files[Math.max(0, i - 1)]);
        } else renderTabs();
        outputs.updateRoots();
        syncLater();
        saveLater();
      });
      tab.append(close);
      tab.addEventListener("click", () => switchTo(f));
      tab.addEventListener("keydown", (e) => {
        const i = files.indexOf(f);
        if (e.key === "ArrowRight" || e.key === "ArrowLeft") {
          const g = files[(i + (e.key === "ArrowRight" ? 1 : files.length - 1)) % files.length];
          switchTo(g);
          (tabs.children[files.indexOf(g)] as HTMLElement)?.focus();
        } else if (e.key === "Enter" || e.key === " ") {
          e.preventDefault();
          switchTo(f);
          view.focus();
        } else if (e.key === "F2" && !f.builtinPath) renameFile(f);
      });
      if (!f.builtinPath) label.addEventListener("dblclick", () => renameFile(f));
      return tab;
    }),
  );
}

function validName(name: string, except?: FileEntry): string | null {
  if (!/^[\w.+-]+\.knl?$/.test(name)) return "A file name ends with .kn or .knl, with no directory";
  if (workspace().some((f) => f !== except && f.name === name)) return `${name} already exists`;
  return null;
}

async function renameFile(f: FileEntry) {
  const name = prompt(`Rename ${f.name} to`, f.name)?.trim();
  if (!name || name === f.name) return;
  const err = validName(name, f);
  if (err) return toast(err);
  const text = textOf(f);
  await closeFile(f);
  const g = newEntry(name, text);
  files.splice(files.length, 0, g);
  if (f === active) active = undefined as unknown as FileEntry;
  switchTo(g);
  outputs.updateRoots();
  syncLater();
}

$("add-file").addEventListener("click", () => {
  const name = prompt("New file (.kn: rules, .knl: declarations)", "new.kn")?.trim();
  if (!name) return;
  const err = validName(name);
  if (err) return toast(err);
  const g = newEntry(name, "");
  files.push(g);
  switchTo(g);
  view.focus();
  outputs.updateRoots();
  syncLater();
});

// ------------------------------------------------------------------ workspace

async function loadWorkspace(next: persist.Files, activeName?: string) {
  for (const f of [...files]) await closeFile(f);
  diagnostics.clear();
  files = next.map(([name, text]) => newEntry(name, text));
  active = undefined as unknown as FileEntry;
  switchTo(files.find((f) => f.name === activeName) ?? files[0]);
  renderProblems();
  outputs.updateRoots();
  syncLater.cancel();
  await flush();
  await lsp?.check();
  refreshOutline();
  outputs.generate();
}

function saveNow() {
  persist.save({
    files: workspace().map((f) => [f.name, textOf(f)]),
    active: active?.builtinPath ? undefined : active?.name,
    backend: outputs.backend.value || undefined,
    root: outputs.root.value || undefined,
  });
}
const saveLater = debounce(saveNow, 400);
addEventListener("pagehide", () => {
  saveLater.cancel();
  saveNow();
});

const templates = $<HTMLSelectElement>("templates");
const group = (label: string, list: typeof examples) =>
  el("optgroup", { label }, ...list.map((e) => el("option", { value: e.id, title: e.description ?? "" }, e.title)));
templates.append(group("Templates", examples.filter((e) => e.template)), group("Tutorial", examples.filter((e) => !e.template)));
templates.addEventListener("change", async () => {
  const ex = exampleById(templates.value);
  templates.value = "";
  if (!ex) return;
  if (!confirm(`Replace the files of the sandbox with "${ex.title}"?`)) return;
  await loadWorkspace(ex.files);
  saveLater();
});

$("share").addEventListener("click", async () => {
  const code = await persist.encode(workspace().map((f) => [f.name, textOf(f)]));
  const url = `${location.origin}${location.pathname}#code=${code}`;
  try {
    await navigator.clipboard.writeText(url);
    toast("Link copied to the clipboard");
  } catch {
    prompt("Copy this link:", url);
  }
});

// ------------------------------------------------------------------ start

const outputs = new Outputs({
  runtime: () => runtime,
  roots: () => {
    const all = workspace().map((f) => [f.name, textOf(f)] as [string, string]);
    return roots(all);
  },
  flush,
  open: (file, line, column) => {
    const f = workspace().find((g) => g.name === file);
    if (f) openLocation({ uri: uriOf(f), range: { start: { line: line - 1, character: column }, end: { line: line - 1, character: column } } });
  },
  changed: () => saveLater(),
});

async function initialFiles(): Promise<{ files: persist.Files; saved?: persist.Saved }> {
  const hash = new URLSearchParams(location.hash.slice(1));
  if (hash.size) history.replaceState(null, "", location.pathname + location.search);
  const code = hash.get("code");
  if (code) {
    try {
      return { files: await persist.decode(code) };
    } catch (e) {
      toast(`Could not read the shared files: ${(e as Error).message}`);
    }
  }
  const ex = exampleById(hash.get("example") ?? "");
  if (ex) return { files: ex.files };
  const saved = persist.load();
  if (saved) return { files: saved.files, saved };
  return { files: exampleById("tiny")!.files };
}

const initial = await initialFiles();
files = initial.files.map(([name, text]) => newEntry(name, text));
switchTo(files.find((f) => f.name === initial.saved?.active) ?? files[0]);
outputs.updateRoots(initial.saved?.root);
renderProblems();

try {
  runtime = await KanonRuntime.load();
  const client = new LspClient(runtime);
  client.onDiagnostics((uri, ds) => {
    diagnostics.set(uri, ds);
    const f = fileByUri(uri);
    if (f) applyDiagnostics(f);
    renderProblems();
  });
  await client.initialize();
  lsp = client;
  const hints = ["<kbd>F12</kbd> or <kbd>Ctrl</kbd>-click: definition"];
  if (lsp.has("referencesProvider")) {
    hints.push("<kbd>Shift</kbd>+<kbd>F12</kbd>: references");
    $("references-tab").hidden = false;
  }
  if (lsp.has("renameProvider")) hints.push("<kbd>F2</kbd>: rename");
  $("hints").innerHTML = hints.join(" · ");
  status.textContent = `kanon ${runtime.info.version}` + (runtime.isMock ? " (mock runtime)" : "");
  status.classList.toggle("mock", runtime.isMock);
  outputs.setBackends(runtime.info.backends, initial.saved?.backend);
  workspace().forEach((f) => (f.dirty = true));
  await flush();
  await lsp.check();
  renderProblems();
  refreshOutline();
  outputs.generate();
} catch (e) {
  console.error(e);
  status.textContent = `The Kanon runtime is unavailable: ${(e as Error).message}`;
  status.classList.add("error");
}
