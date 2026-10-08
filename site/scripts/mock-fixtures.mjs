// Regenerates mock/fixtures.json, the canned outputs of the mock runtime: the
// output of every backend (every part of the generated code, as the runtime of
// web/ prints it) on every example of examples/index.json. It is made of the
// files that a native kanon writes, with `kanon ocaml DIR` and `kanon lean DIR`
// (see parts.mjs), by $KANON, or kanon in PATH; e.g.
// KANON=../_build/install/default/bin/kanon after `dune build`.

import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { backends, nativeParts } from "./parts.mjs";

const site = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const kanon = process.env.KANON ?? "kanon";
const { examples } = JSON.parse(readFileSync(join(site, "examples/index.json"), "utf8"));

// The files that no other file uses, as the sandbox picks them (src/roots.ts).
function roots(files) {
  const used = new Set();
  for (const text of Object.values(files))
    for (const m of text.matchAll(/^\s*use\s+"([^"]+)"/gm)) {
      used.add(`${m[1]}.knl`);
      used.add(`${m[1]}.kn`);
    }
  return Object.keys(files).filter((f) => f.endsWith(".knl") && !used.has(f));
}

const runs = [];
for (const ex of examples) {
  const files = {};
  for (const [name, path] of Object.entries(ex.files))
    files[name] = readFileSync(join(site, path), "utf8");
  const dir = mkdtempSync(join(tmpdir(), "kanon-fixture-"));
  for (const [name, text] of Object.entries(files)) writeFileSync(join(dir, name), text);
  const text = Object.values(files).join("\n");
  for (const root of roots(files))
    runs.push({ example: ex.id, root, files, outputs: nativeParts(kanon, dir, [root], text) });
  rmSync(dir, { recursive: true, force: true });
}

const out = join(site, "mock/fixtures.json");
writeFileSync(out, JSON.stringify({ backends, runs }) + "\n");
console.log(`wrote ${out} (${runs.length} runs)`);
