// A client of Kanon's language server, which runs in the runtime's worker:
// every message in returns the messages that the server sent while handling
// it, which are dispatched here (responses to their requests, diagnostics to
// the listeners).

import type { KanonRuntime, LspMessage } from "./client";

export interface Position {
  line: number;
  character: number;
}
export interface Range {
  start: Position;
  end: Position;
}
export interface Location {
  uri: string;
  range: Range;
}
export interface Diagnostic {
  range: Range;
  severity?: 1 | 2 | 3 | 4;
  message: string;
  source?: string;
}
export interface TextEdit {
  range: Range;
  newText: string;
}

export class LspClient {
  capabilities: Record<string, any> = {};
  private next = 1;
  private diagnosticListeners: ((uri: string, diagnostics: Diagnostic[]) => void)[] = [];
  private versions = new Map<string, number>();

  constructor(readonly runtime: KanonRuntime) {}

  get rootUri() {
    return "file://" + this.runtime.info.root;
  }

  onDiagnostics(f: (uri: string, diagnostics: Diagnostic[]) => void) {
    this.diagnosticListeners.push(f);
  }

  /** Handles the messages of the server; the response to `id`, if any. */
  private async dispatch(messages: LspMessage[], id?: number): Promise<LspMessage | undefined> {
    let response: LspMessage | undefined;
    for (const m of messages) {
      if (m.method === "textDocument/publishDiagnostics") {
        for (const f of this.diagnosticListeners) f(m.params.uri, m.params.diagnostics);
      } else if (m.method !== undefined && m.id !== undefined) {
        // a request of the server (e.g. workspace/configuration): not supported
        await this.dispatch(await this.runtime.lsp({ jsonrpc: "2.0", id: m.id, result: null }));
      } else if (m.method === "window/logMessage" || m.method === "window/showMessage") {
        console.info("kanon lsp:", m.params?.message);
      } else if (m.id !== undefined && m.id === id) {
        response = m;
      }
    }
    return response;
  }

  async request<T = any>(method: string, params: object): Promise<T | null> {
    const id = this.next++;
    const r = await this.dispatch(await this.runtime.lsp({ jsonrpc: "2.0", id, method, params }), id);
    if (!r) return null;
    if (r.error) throw new Error(`${method}: ${r.error.message}`);
    return r.result as T;
  }

  async notify(method: string, params: object): Promise<void> {
    await this.dispatch(await this.runtime.lsp({ jsonrpc: "2.0", method, params }));
  }

  /** Runs the pending check, which publishes the diagnostics. */
  async check(): Promise<void> {
    await this.dispatch(await this.runtime.check());
  }

  async initialize() {
    const r = await this.request("initialize", {
      processId: null,
      rootUri: this.rootUri,
      workspaceFolders: [{ uri: this.rootUri, name: "sandbox" }],
      capabilities: {
        textDocument: {
          synchronization: { didSave: false },
          hover: { contentFormat: ["markdown", "plaintext"] },
          completion: { completionItem: { documentationFormat: ["markdown", "plaintext"] } },
          definition: {},
          references: {},
          documentHighlight: {},
          documentSymbol: { hierarchicalDocumentSymbolSupport: true },
          rename: { prepareSupport: true },
          publishDiagnostics: {},
        },
        workspace: { symbol: {}, workspaceFolders: true, workspaceEdit: { documentChanges: false } },
      },
    });
    this.capabilities = r?.capabilities ?? {};
    await this.notify("initialized", {});
  }

  /** Whether the server provides `name` (e.g. "renameProvider"). */
  has(name: string): boolean {
    const c = this.capabilities[name];
    return c !== undefined && c !== false && c !== null;
  }

  didOpen(uri: string, text: string) {
    this.versions.set(uri, 1);
    return this.notify("textDocument/didOpen", { textDocument: { uri, languageId: "kanon", version: 1, text } });
  }

  didChange(uri: string, text: string) {
    const version = (this.versions.get(uri) ?? 1) + 1;
    this.versions.set(uri, version);
    return this.notify("textDocument/didChange", { textDocument: { uri, version }, contentChanges: [{ text }] });
  }

  didClose(uri: string) {
    this.versions.delete(uri);
    return this.notify("textDocument/didClose", { textDocument: { uri } });
  }
}

/** A Location, a Location[] or a LocationLink[], as Locations. */
export function locations(r: any): Location[] {
  if (!r) return [];
  const all = Array.isArray(r) ? r : [r];
  return all.map((l) => ("targetUri" in l ? { uri: l.targetUri, range: l.targetSelectionRange ?? l.targetRange } : l));
}
