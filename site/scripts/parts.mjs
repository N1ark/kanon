// The parts of the generated code, from the files of a native kanon: what the
// runtime of web/ prints for each of its backends (see Parts in src/parts.ml),
// made of the files that `kanon ocaml DIR` and `kanon lean DIR` write. Used by
// mock-fixtures.mjs and by web/test.mjs.

import { execFileSync } from "node:child_process";
import { mkdtempSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, relative } from "node:path";

export const backends = [
  "ocaml-types",
  "ocaml",
  "ocaml-typed",
  "ocaml-tests",
  "lean-types",
  "lean-node",
  "lean-lang",
  "lean-model",
  "lean-statements",
  "lean-soundness",
  "lean-syntax",
  "lean-semantics",
  "lean-rules",
];

/** What the runtime prints for a wrong command line. */
export const usage = `usage: BACKEND FILE...\nThe backends are ${backends.join(", ")}.\n`;

/** Runs `kanon cmd out args` in cwd: the exit code and the standard error. */
function generate(kanon, cmd, cwd, out, args) {
  try {
    execFileSync(kanon, [cmd, out, ...args], {
      cwd,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    });
    return { code: 0, stderr: "" };
  } catch (e) {
    // the usage of the runtime is that of its backends
    const stderr = (e.stderr ?? String(e)).replace(/usage: kanon ocaml[^]*$/, usage);
    return { code: e.status ?? 1, stderr };
  }
}

/** The files under dir, recursively, sorted by path. */
function tree(dir) {
  const files = [];
  for (const n of readdirSync(dir)) {
    const p = join(dir, n);
    if (statSync(p).isDirectory()) files.push(...tree(p));
    else files.push(p);
  }
  return files.sort();
}

/** The Lean files of each part, by path under the output directory (see
    Gen_lean.parts). */
const leanParts = {
  "lean-types": (f) => f.endsWith("/Types.lean"),
  "lean-node": (f) => f.endsWith("/Node.lean"),
  "lean-lang": (f) => f.endsWith("/Lang.lean"),
  "lean-model": (f) => f.endsWith("/Model.lean"),
  "lean-statements": (f) => f.endsWith("/Lift.lean") || f.includes("/Statements/"),
  "lean-soundness": (f) => f.endsWith("/Soundness.lean") || f.includes("/Soundness/"),
  "lean-syntax": (f) => f.endsWith("/Syntax.lean"),
  "lean-semantics": (f) => f.endsWith("/Semantics.lean"),
  "lean-rules": (f) => f.endsWith("/Rules.lean"),
};

/** The files of a part of Lean, one after the other, each after its name if
    they are several. */
function leanOutput(out, backend) {
  const files = tree(join(out, "Generated"))
    .map((p) => relative(out, p))
    .filter(leanParts[backend]);
  return files
    .map((f, i) => {
      const text = readFileSync(join(out, f), "utf8");
      return files.length > 1 ? `${i > 0 ? "\n" : ""}-- ${f}\n\n${text}` : text;
    })
    .join("");
}

/** The OCaml file of a module that the language declares (with
    [@@@ocaml_types "M"]), or the default one. */
function moduleFile(m, dflt) {
  return m ? `${m[0].toLowerCase()}${m.slice(1)}.ml` : dflt;
}

/**
 * The output of each backend on [args] (the files of the language, then the
 * files of the rules), run by [kanon] in [cwd]: { code, stdout, stderr }. [text]
 * is the text of the files of the language, where the OCaml modules are
 * declared.
 */
export function nativeParts(kanon, cwd, args, text) {
  const dir = mkdtempSync(join(tmpdir(), "kanon-parts-"));
  try {
    const attr = (a) => text.match(new RegExp(`\\[@@@${a} "([A-Za-z0-9_]+)"\\]`))?.[1];
    const ocamlFiles = {
      "ocaml-types": moduleFile(attr("ocaml_types"), "types.ml"),
      ocaml: moduleFile(attr("ocaml_rules"), "rules.ml"),
      "ocaml-typed": attr("ocaml_rules") ? "typed.ml" : undefined,
      "ocaml-tests": "tests.ml",
    };
    // kanon ocaml needs rules: a language without any only has its types
    let rules = true;
    let ocaml = generate(kanon, "ocaml", cwd, join(dir, "ocaml"), args);
    if (ocaml.code === 2) {
      rules = false;
      writeFileSync(join(dir, "no_rules.kn"), "");
      ocaml = generate(kanon, "ocaml", cwd, join(dir, "ocaml"), [...args, join(dir, "no_rules.kn")]);
    }
    const lean = generate(kanon, "lean", cwd, join(dir, "lean"), args);
    const outputs = {};
    for (const backend of backends) {
      const isLean = backend.startsWith("lean-");
      const result = isLean ? lean : ocaml;
      let { code, stderr } = result;
      let stdout = "";
      if (code === 0 && !rules && backend !== "ocaml-types" && !isLean) {
        code = 2;
        stderr = usage;
      } else if (code === 0 && backend === "ocaml-typed" && !ocamlFiles[backend]) {
        code = 1;
        stderr =
          'kanon: ocaml-typed: [@@@ocaml_rules "M"], in the declaration of the language, names the OCaml module of the rules (the output of kanon ocaml), which the implementation is made of\n';
      } else if (code === 0)
        stdout = isLean
          ? leanOutput(join(dir, "lean"), backend)
          : readFileSync(join(dir, "ocaml/Generated", ocamlFiles[backend]), "utf8");
      outputs[backend] = { code, stdout, stderr };
    }
    return outputs;
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}
