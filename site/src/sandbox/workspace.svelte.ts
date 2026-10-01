// The sandbox's state: its files (one CodeMirror state each, swapped into the one editor), the
// runtime and its language server, kept in sync with the files, and what the server says about
// them. The components render it; CodeMirror and the server are driven from here.

import { setDiagnostics, type Diagnostic as CmDiagnostic } from "@codemirror/lint";
import { EditorState } from "@codemirror/state";
import { EditorView } from "@codemirror/view";
import { confirmAction, promptText, toast } from "purr";
import { roots } from "../examples";
import type { KanonSyntax } from "../highlight/kanon";
import { debounce } from "../lib/util";
import { KanonRuntime } from "../runtime/client";
import type { RuntimeInfo } from "../runtime/protocol";
import { LspClient, locations, type Diagnostic, type Location, type Range, type TextEdit } from "../runtime/lsp";
import { kanonExtensions, toOffsets, toPosition, type LspHost } from "./editor";
import * as persist from "./persist";

export interface FileEntry {
  name: string;
  state: EditorState;
  /** A read-only file of a built-in module, at this path of the runtime. */
  builtinPath?: string;
  /** Changed since it was last sent to the runtime. */
  dirty: boolean;
  /** Opened in the language server. */
  opened: boolean;
}

export interface Symbol {
  name: string;
  detail?: string;
  depth: number;
  range: Range;
}

const uriToPath = (uri: string) => decodeURIComponent(uri.replace(/^file:\/\//, ""));

export class Workspace {
  files = $state.raw<FileEntry[]>([]);
  active = $state.raw<FileEntry | null>(null);
  /** By URI, as the server last published them. */
  diagnostics = $state.raw(new Map<string, Diagnostic[]>());
  references = $state.raw<Location[] | null>(null);
  panel = $state<"problems" | "references">("problems");
  status = $state<"loading" | "ready" | "failed">("loading");
  error = $state("");
  info = $state.raw<RuntimeInfo | null>(null);
  capabilities = $state.raw<Record<string, unknown>>({});
  /** Bumped after each check: the files changed, and the server has seen them. */
  revision = $state(0);

  runtime = $state.raw<KanonRuntime | null>(null);
  lsp: LspClient | null = null;
  view!: EditorView;
  private flushing: Promise<void> = Promise.resolve();

  constructor(readonly syntax: KanonSyntax | null) {}

  // ---------------------------------------------------------------- files

  root = () => this.info?.root ?? "/sandbox";
  pathOf = (f: FileEntry) => f.builtinPath ?? `${this.root()}/${f.name}`;
  uriOf = (f: FileEntry) => "file://" + this.pathOf(f);
  workspace = () => this.files.filter((f) => !f.builtinPath);
  stateOf = (f: FileEntry) => (f === this.active ? this.view.state : f.state);
  textOf = (f: FileEntry) => this.stateOf(f).doc.toString();
  fileByUri = (uri: string) => this.files.find((f) => this.uriOf(f) === uri);
  has = (capability: string) => {
    const c = this.capabilities[capability];
    return c !== undefined && c !== false && c !== null;
  };

  /** The root files of the language: its .knl files that no other file uses. */
  roots = () => roots(this.workspace().map((f) => [f.name, this.textOf(f)] as [string, string]));

  /** The files, as saved and shared. */
  snapshot = (): persist.Files => this.workspace().map((f) => [f.name, this.textOf(f)]);

  private entry(name: string, text: string, builtinPath?: string): FileEntry {
    const f: FileEntry = { name, builtinPath, dirty: true, opened: false, state: undefined as unknown as EditorState };
    f.state = EditorState.create({
      doc: text,
      extensions: kanonExtensions(this.hostFor(f), !!builtinPath, (u) => {
        if (u.docChanged) this.edited(f);
      }),
    });
    return f;
  }

  private hostFor(f: FileEntry): LspHost {
    return {
      lsp: () => this.lsp,
      uri: () => this.uriOf(f),
      flush: () => this.flush(),
      syntax: this.syntax,
      goToDefinition: (view, pos) => this.goToDefinition(f, view, pos),
      findReferences: (view, pos) => this.findReferences(f, view, pos),
      rename: (view, pos) => this.rename(f, view, pos),
    };
  }

  switchTo(f: FileEntry) {
    if (f !== this.active) {
      if (this.active) this.active.state = this.view.state;
      this.active = f;
      this.view.setState(f.state);
    }
    this.saveLater();
  }

  private edited(f: FileEntry) {
    if (f.builtinPath) return;
    f.dirty = true;
    this.syncLater();
    this.saveLater();
  }

  // ---------------------------------------------------------------- sync

  /** Sends the changed files to the runtime and to the language server. */
  flush(): Promise<void> {
    this.flushing = this.flushing.then(async () => {
      const { runtime, lsp } = this;
      if (!runtime || !lsp) return;
      for (const f of this.workspace()) {
        if (!f.dirty) continue;
        f.dirty = false;
        const text = this.textOf(f);
        await runtime.writeFile(this.pathOf(f), text);
        if (f.opened) await lsp.didChange(this.uriOf(f), text);
        else {
          f.opened = true;
          await lsp.didOpen(this.uriOf(f), text);
        }
      }
    });
    return this.flushing;
  }

  /** Sends the changes, then checks the language: the server publishes its diagnostics. */
  async sync() {
    this.syncLater.cancel();
    await this.flush();
    if (!this.lsp) return;
    await this.lsp.check();
    this.revision++;
  }

  readonly syncLater = debounce(() => this.sync(), 200);

  private async close(f: FileEntry) {
    this.files = this.files.filter((g) => g !== f);
    const uri = this.uriOf(f);
    this.setDiagnostics(uri, undefined);
    if (f.builtinPath || !this.runtime || !this.lsp) return;
    await this.flush();
    await this.runtime.removeFile(this.pathOf(f));
    if (f.opened) await this.lsp.didClose(uri);
    // the other files may have used it
    this.workspace().forEach((g) => (g.dirty = true));
  }

  // ---------------------------------------------------------------- diagnostics

  private setDiagnostics(uri: string, ds: Diagnostic[] | undefined) {
    const next = new Map(this.diagnostics);
    if (ds?.length) next.set(uri, ds);
    else next.delete(uri);
    this.diagnostics = next;
    const f = this.fileByUri(uri);
    if (f) this.applyDiagnostics(f);
  }

  private applyDiagnostics(f: FileEntry) {
    const state = this.stateOf(f);
    const doc = state.doc;
    const cm: CmDiagnostic[] = (this.diagnostics.get(this.uriOf(f)) ?? []).map((d) => {
      let { from, to } = toOffsets(doc, d.range);
      if (to === from) to = Math.min(doc.length, from + 1);
      if (to === from && from > 0) from--;
      return { from, to, severity: severity(d), message: d.message, source: d.source };
    });
    if (f === this.active) this.view.dispatch(setDiagnostics(state, cm));
    else f.state = state.update(setDiagnostics(state, cm)).state;
  }

  errorsIn = (f: FileEntry) => (this.diagnostics.get(this.uriOf(f)) ?? []).filter((d) => severity(d) === "error").length;

  // ---------------------------------------------------------------- navigation

  async openLocation(loc: Location) {
    const path = uriToPath(loc.uri);
    let f = this.files.find((g) => this.pathOf(g) === path);
    if (!f) {
      // a file of a built-in module: read-only
      if (!this.runtime) return;
      const name = path.slice(path.lastIndexOf("/") + 1);
      const text = (await this.runtime.readFile(path)) ?? this.runtime.info.builtins[name];
      if (text === undefined) {
        toast(`Cannot open ${path}`, { kind: "error" });
        return;
      }
      f = this.entry(name, text, path);
      this.files = [...this.files, f];
    }
    this.switchTo(f);
    const { from } = toOffsets(this.view.state.doc, loc.range);
    this.view.dispatch({ selection: { anchor: from }, effects: EditorView.scrollIntoView(from, { y: "center" }) });
    this.view.focus();
  }

  /** Opens a location given as kanon prints it: a file name, a line from 1, a column from 0. */
  openFileAt(name: string, line: number, column: number) {
    const f = this.workspace().find((g) => g.name === name);
    if (!f) return;
    const at = { line: line - 1, character: column };
    this.openLocation({ uri: this.uriOf(f), range: { start: at, end: at } });
  }

  async goToDefinition(f: FileEntry, view: EditorView, pos: number) {
    if (!this.lsp || !this.has("definitionProvider")) return;
    await this.flush();
    const r = await this.lsp.request("textDocument/definition", {
      textDocument: { uri: this.uriOf(f) },
      position: toPosition(view.state.doc, pos),
    });
    const locs = locations(r);
    if (locs.length) this.openLocation(locs[0]);
    else toast("No definition found");
  }

  async findReferences(f: FileEntry, view: EditorView, pos: number) {
    if (!this.lsp || !this.has("referencesProvider")) return;
    await this.flush();
    const r: Location[] | null = await this.lsp.request("textDocument/references", {
      textDocument: { uri: this.uriOf(f) },
      position: toPosition(view.state.doc, pos),
      context: { includeDeclaration: true },
    });
    this.references = r ?? [];
    this.panel = "references";
  }

  /** The line of a location, for the lists. */
  lineAt(loc: Location): string {
    const f = this.fileByUri(loc.uri);
    if (!f) return "";
    const doc = this.stateOf(f).doc;
    return loc.range.start.line < doc.lines ? doc.line(loc.range.start.line + 1).text.trim() : "";
  }

  nameOf(uri: string): string {
    return this.fileByUri(uri)?.name ?? uriToPath(uri).split("/").pop()!;
  }

  async rename(f: FileEntry, view: EditorView, pos: number) {
    if (!this.lsp || !this.has("renameProvider") || f.builtinPath) return;
    const word = view.state.wordAt(pos);
    const old = word ? view.state.sliceDoc(word.from, word.to) : "";
    const name = await promptText(`Rename ${old}`, { label: "New name", value: old }, { confirm: "Rename" });
    if (!name || name === old) return;
    await this.flush();
    let edit: any;
    try {
      edit = await this.lsp.request("textDocument/rename", {
        textDocument: { uri: this.uriOf(f) },
        position: toPosition(view.state.doc, pos),
        newName: name,
      });
    } catch (e) {
      toast((e as Error).message, { kind: "error" });
      return;
    }
    if (!edit) return void toast("Nothing to rename here");
    const byUri: [string, TextEdit[]][] = edit.documentChanges
      ? edit.documentChanges.filter((c: any) => c.textDocument).map((c: any) => [c.textDocument.uri, c.edits])
      : Object.entries(edit.changes ?? {});
    for (const [uri, edits] of byUri) {
      const g = this.fileByUri(uri);
      if (!g || g.builtinPath) continue;
      const state = this.stateOf(g);
      const changes = edits.map((e) => ({ ...toOffsets(state.doc, e.range), insert: e.newText }));
      if (g === this.active) this.view.dispatch({ changes });
      else {
        g.state = state.update({ changes }).state;
        this.edited(g);
      }
    }
  }

  /** The outline of the current file, flattened. */
  async symbols(): Promise<Symbol[]> {
    const f = this.active;
    if (!f || !this.lsp || !this.has("documentSymbolProvider")) return [];
    await this.flush();
    const r: any[] | null = await this.lsp
      .request("textDocument/documentSymbol", { textDocument: { uri: this.uriOf(f) } })
      .catch(() => null);
    const out: Symbol[] = [];
    const add = (s: any, depth: number) => {
      out.push({ name: s.name, detail: s.detail, depth, range: s.selectionRange ?? s.range ?? s.location.range });
      for (const c of s.children ?? []) add(c, depth + 1);
    };
    for (const s of r ?? []) add(s, 0);
    return out;
  }

  // ---------------------------------------------------------------- files

  private nameError(name: string, except?: FileEntry): string | null {
    if (!/^[\w.+-]+\.knl?$/.test(name)) return "A file name ends with .kn or .knl, with no directory";
    if (this.workspace().some((f) => f !== except && f.name === name)) return `${name} already exists`;
    return null;
  }

  async addFile() {
    const name = await promptText(
      "New file",
      { label: "Name", value: "new.kn", hint: ".knl: declarations; .kn: rules, primitives and helpers" },
      { confirm: "Create" },
    );
    if (!name) return;
    const err = this.nameError(name);
    if (err) return void toast(err, { kind: "error" });
    const f = this.entry(name, "");
    this.files = [...this.files, f];
    this.switchTo(f);
    this.view.focus();
    this.syncLater();
  }

  async renameFile(f: FileEntry) {
    if (f.builtinPath) return;
    const name = await promptText(`Rename ${f.name}`, { label: "Name", value: f.name }, { confirm: "Rename" });
    if (!name || name === f.name) return;
    const err = this.nameError(name, f);
    if (err) return void toast(err, { kind: "error" });
    const text = this.textOf(f);
    const i = this.files.indexOf(f);
    const wasActive = f === this.active;
    await this.close(f);
    const g = this.entry(name, text);
    this.files = [...this.files.slice(0, i), g, ...this.files.slice(i)];
    if (wasActive) {
      this.active = null;
      this.switchTo(g);
    }
    this.syncLater();
  }

  async closeFile(f: FileEntry) {
    if (!f.builtinPath) {
      if (this.workspace().length === 1) return void toast("A language needs at least one file");
      const sure = await confirmAction(`Delete ${f.name}?`, { confirmLabel: "Delete", danger: true });
      if (!sure) return;
    }
    const i = this.files.indexOf(f);
    await this.close(f);
    if (f === this.active) {
      this.active = null;
      this.switchTo(this.files[Math.max(0, i - 1)]);
    }
    this.syncLater();
    this.saveLater();
  }

  /** Replaces the files: a template, or shared ones. */
  async load(files: persist.Files, activeName?: string) {
    for (const f of [...this.files]) await this.close(f);
    this.files = files.map(([name, text]) => this.entry(name, text));
    this.active = null;
    this.references = null;
    this.switchTo(this.files.find((f) => f.name === activeName) ?? this.files[0]);
    await this.sync();
  }

  // ---------------------------------------------------------------- persistence

  saved: persist.Saved | null = null;
  /** The output panel's choices, saved with the files. */
  outputChoice: { backend?: string; root?: string } = {};

  saveNow() {
    persist.save({
      files: this.snapshot(),
      active: this.active?.builtinPath ? undefined : this.active?.name,
      ...this.outputChoice,
    });
  }

  readonly saveLater = debounce(() => this.saveNow(), 400);

  async shareUrl(): Promise<string> {
    const code = await persist.encode(this.snapshot());
    return `${location.origin}${location.pathname}#code=${code}`;
  }

  // ---------------------------------------------------------------- start

  /** Shows the first files, then starts the runtime and its language server. */
  async start(view: EditorView, initial: persist.Files, saved: persist.Saved | null) {
    this.view = view;
    this.saved = saved;
    this.outputChoice = { backend: saved?.backend, root: saved?.root };
    this.files = initial.map(([name, text]) => this.entry(name, text));
    this.switchTo(this.files.find((f) => f.name === saved?.active) ?? this.files[0]);
    addEventListener("pagehide", () => {
      this.saveLater.cancel();
      this.saveNow();
    });
    try {
      const runtime = await KanonRuntime.load();
      const lsp = new LspClient(runtime);
      lsp.onDiagnostics((uri, ds) => this.setDiagnostics(uri, ds));
      this.runtime = runtime;
      this.info = runtime.info;
      await lsp.initialize();
      this.lsp = lsp;
      this.capabilities = lsp.capabilities;
      this.workspace().forEach((f) => (f.dirty = true));
      await this.sync();
      this.status = "ready";
    } catch (e) {
      console.error(e);
      this.error = (e as Error).message;
      this.status = "failed";
    }
  }
}

export function severity(d: Diagnostic): "error" | "warning" | "info" {
  return d.severity === 2 ? "warning" : d.severity === 3 || d.severity === 4 ? "info" : "error";
}
