// Builds the tree-sitter grammar of the repository (../tree-sitter-kanon) to
// WebAssembly, public/tree-sitter-kanon.wasm, with the tree-sitter CLI of
// node_modules (the version that generated the grammar, and of
// web-tree-sitter). The CLI compiles with emcc when it is in PATH (or in
// $EMSDK, an activated emsdk), and otherwise in docker or podman.

import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync } from "node:fs";
import { delimiter, dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const site = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const grammar = resolve(site, "../tree-sitter-kanon");
const out = join(site, "public", "tree-sitter-kanon.wasm");
const cli = join(site, "node_modules", "tree-sitter-cli", "cli.js");

const path = (process.env.PATH ?? "").split(delimiter);
if (process.env.EMSDK) {
  path.unshift(process.env.EMSDK, join(process.env.EMSDK, "upstream", "emscripten"));
}

mkdirSync(dirname(out), { recursive: true });
execFileSync(process.execPath, [cli, "build", "--wasm", "-o", out, "."], {
  cwd: grammar,
  stdio: "inherit",
  env: { ...process.env, PATH: path.join(delimiter) },
});
if (!existsSync(out)) throw new Error(`${out} was not built`);
console.log(`built ${out}`);
