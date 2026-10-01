// The Web Worker that hosts Kanon's web runtime: a classic worker, so that it
// can load kanon.js with importScripts. It only imports types (a classic
// worker cannot import modules): the protocol is in protocol.ts.
//
// Messages in: { type: "load", url } once, then { id, op, args } calls of the
// API of globalThis.kanon. Messages out: { type: "ready", info } or
// { type: "failed", error }, then { id, result } or { id, error }.

import type { KanonApi, ToMain, ToWorker } from "./protocol";

declare function importScripts(...urls: string[]): void;

const scope = globalThis as unknown as {
  kanon?: KanonApi;
  onkanonready?: () => void;
  postMessage(m: ToMain): void;
  onmessage: ((e: MessageEvent<ToWorker>) => void) | null;
};

const post = (m: ToMain) => scope.postMessage(m);
let ready = false;

function load(url: string) {
  const done = () => {
    const k = scope.kanon;
    if (ready || !k) return;
    ready = true;
    post({ type: "ready", info: { version: k.version, root: k.root, backends: k.backends, builtins: k.builtins } });
  };
  // initialisation may be asynchronous: the runtime calls onkanonready when it
  // is done, or has already defined kanon after importScripts
  scope.onkanonready = done;
  try {
    importScripts(url);
  } catch (e) {
    post({ type: "failed", error: `could not load ${url}: ${e}` });
    return;
  }
  done();
}

scope.onmessage = (e) => {
  const m = e.data;
  if ("type" in m) {
    load(m.url);
    return;
  }
  const k = scope.kanon;
  try {
    if (!k) throw new Error("the Kanon runtime is not loaded");
    const f = k[m.op] as unknown as (...args: unknown[]) => unknown;
    post({ id: m.id, result: f.apply(k, m.args) });
  } catch (err) {
    post({ id: m.id, error: err instanceof Error ? `${err.message}` : String(err) });
  }
};
