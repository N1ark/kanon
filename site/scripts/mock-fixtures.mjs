// Regenerates mock/fixtures.json, the canned outputs of the mock runtime: the
// output of every backend on every example of examples/index.json, computed by
// a native kanon ($KANON, or kanon in PATH; e.g.
// KANON=../_build/default/install/bin/kanon after `dune build`).

import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const site = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const kanon = process.env.KANON ?? "kanon";
const backends = [
  "ocaml-types",
  "ocaml",
  "ocaml-tests",
  "lean-types",
  "lean-syntax",
  "lean-signatures",
  "lean-typing",
  "lean-model",
  "lean-statements",
  "lean-lifts",
  "lean-soundness",
];
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
  for (const root of roots(files)) {
    const outputs = {};
    for (const backend of backends) {
      let code = 0;
      let stdout = "";
      let stderr = "";
      try {
        stdout = execFileSync(kanon, [backend, root], {
          cwd: dir,
          encoding: "utf8",
          stdio: ["ignore", "pipe", "pipe"],
          maxBuffer: 64 << 20,
        });
      } catch (e) {
        code = e.status ?? 1;
        stdout = e.stdout ?? "";
        stderr = e.stderr ?? String(e);
      }
      outputs[backend] = { code, stdout, stderr };
    }
    runs.push({ example: ex.id, root, files, outputs });
  }
  rmSync(dir, { recursive: true, force: true });
}

const out = join(site, "mock/fixtures.json");
writeFileSync(out, JSON.stringify({ backends, runs }) + "\n");
console.log(`wrote ${out} (${runs.length} runs)`);
