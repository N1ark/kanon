// The page's side of the runtime: starts the worker, which loads kanon.js from
// kanon/ next to the pages (copied there by the build, see vite.config.ts),
// and turns the calls of its API into promises. The worker handles them in
// order.

import type { Op, RunResult, RuntimeInfo, ToMain, ToWorker } from "./protocol";

export class KanonRuntime {
  private worker: Worker;
  private next = 0;
  private pending = new Map<number, { resolve: (v: unknown) => void; reject: (e: Error) => void }>();
  info!: RuntimeInfo;

  private constructor(worker: Worker) {
    this.worker = worker;
  }

  /** The URL of the runtime's script. */
  static url = new URL("kanon/kanon.js", document.baseURI).href;

  private static loading: Promise<KanonRuntime> | undefined;

  /** The runtime, loaded once per page. */
  static load(): Promise<KanonRuntime> {
    this.loading ??= new Promise((resolve, reject) => {
      const worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "classic", name: "kanon" });
      const rt = new KanonRuntime(worker);
      const timeout = setTimeout(() => reject(new Error("the Kanon runtime did not start in time")), 120_000);
      worker.onerror = (e) => {
        clearTimeout(timeout);
        reject(new Error(e.message || "the Kanon worker failed"));
      };
      worker.onmessage = (e: MessageEvent<ToMain>) => {
        const m = e.data;
        if ("type" in m) {
          clearTimeout(timeout);
          if (m.type === "ready") {
            rt.info = m.info;
            worker.onmessage = (e: MessageEvent<ToMain>) => rt.receive(e.data);
            resolve(rt);
          } else reject(new Error(m.error));
        }
      };
      worker.postMessage({ type: "load", url: KanonRuntime.url } satisfies ToWorker);
    });
    return this.loading;
  }

  private receive(m: ToMain) {
    if ("type" in m) return;
    const p = this.pending.get(m.id);
    if (!p) return;
    this.pending.delete(m.id);
    if (m.error !== undefined) p.reject(new Error(m.error));
    else p.resolve(m.result);
  }

  private call<T>(op: Op, ...args: unknown[]): Promise<T> {
    const id = this.next++;
    return new Promise<T>((resolve, reject) => {
      this.pending.set(id, { resolve: resolve as (v: unknown) => void, reject });
      this.worker.postMessage({ id, op, args } satisfies ToWorker);
    });
  }

  get isMock() {
    return this.info.version === "mock";
  }

  writeFile(path: string, contents: string) {
    return this.call<void>("writeFile", path, contents);
  }
  removeFile(path: string) {
    return this.call<void>("removeFile", path);
  }
  readFile(path: string) {
    return this.call<string | null>("readFile", path);
  }
  listFiles(dir: string) {
    return this.call<string[]>("listFiles", dir);
  }
  /** One JSON-RPC message to the language server; the messages it sent. */
  async lsp(message: object): Promise<LspMessage[]> {
    const out = await this.call<string[]>("lsp", JSON.stringify(message));
    return out.map((s) => JSON.parse(s));
  }
  async check(): Promise<LspMessage[]> {
    const out = await this.call<string[]>("check");
    return out.map((s) => JSON.parse(s));
  }
  run(args: string[]) {
    return this.call<RunResult>("run", args);
  }
}

export interface LspMessage {
  jsonrpc: "2.0";
  id?: number | string;
  method?: string;
  params?: any;
  result?: any;
  error?: { code: number; message: string };
}
