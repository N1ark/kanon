// The files of the sandbox, saved in localStorage, and shared in the hash of
// its URL: #code= the deflated JSON of the files, in base64url.

import { storage } from "../util";

export type Files = [string, string][];

export interface Saved {
  files: Files;
  active?: string;
  backend?: string;
  root?: string;
}

const KEY = "kanon-sandbox-v1";

export function load(): Saved | null {
  const s = storage.get(KEY);
  if (!s) return null;
  try {
    const v = JSON.parse(s) as Saved;
    return Array.isArray(v.files) && v.files.length ? v : null;
  } catch {
    return null;
  }
}

export function save(v: Saved) {
  storage.set(KEY, JSON.stringify(v));
}

function toBase64Url(bytes: Uint8Array): string {
  let s = "";
  for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

function fromBase64Url(s: string): Uint8Array {
  const b = atob(s.replace(/-/g, "+").replace(/_/g, "/"));
  return Uint8Array.from(b, (c) => c.charCodeAt(0));
}

async function pipe(bytes: Uint8Array, stream: CompressionStream | DecompressionStream): Promise<Uint8Array> {
  const out = new Blob([bytes as BlobPart]).stream().pipeThrough(stream);
  return new Uint8Array(await new Response(out).arrayBuffer());
}

export async function encode(files: Files): Promise<string> {
  const json = new TextEncoder().encode(JSON.stringify({ v: 1, files }));
  return toBase64Url(await pipe(json, new CompressionStream("deflate-raw")));
}

export async function decode(code: string): Promise<Files> {
  const json = await pipe(fromBase64Url(code), new DecompressionStream("deflate-raw"));
  const v = JSON.parse(new TextDecoder().decode(json));
  if (!Array.isArray(v.files) || !v.files.every((f: unknown) => Array.isArray(f) && f.length === 2))
    throw new Error("not a list of files");
  return v.files;
}
