/** The API of Kanon's web runtime, globalThis.kanon in its worker (see
 * web/ in the repository). Strings are JSON or text. */
export interface KanonApi {
  version: string;
  /** The directory of the user's files in the virtual file system; the LSP
   * rootUri is "file://" + root. */
  root: string;
  writeFile(path: string, contents: string): void;
  removeFile(path: string): void;
  readFile(path: string): string | null;
  listFiles(dir: string): string[];
  /** One JSON-RPC message in; the messages that the server sent while
   * handling it out (responses and notifications). */
  lsp(message: string): string[];
  /** Runs the pending (debounced) check; returns the messages sent
   * (textDocument/publishDiagnostics). */
  check(): string[];
  /** `kanon ARGS...` */
  run(args: string[]): RunResult;
  backends: string[];
  /** The built-in modules, by file name: bool.knl, bool.kn. */
  builtins: Record<string, string>;
}

export interface RunResult {
  code: number;
  stdout: string;
  stderr: string;
}

export type Op = "writeFile" | "removeFile" | "readFile" | "listFiles" | "lsp" | "check" | "run";

export interface RuntimeInfo {
  version: string;
  root: string;
  backends: string[];
  builtins: Record<string, string>;
}

export type ToWorker = { type: "load"; url: string } | { id: number; op: Op; args: unknown[] };

export type ToMain =
  | { type: "ready"; info: RuntimeInfo }
  | { type: "failed"; error: string }
  | { id: number; result?: unknown; error?: string };
