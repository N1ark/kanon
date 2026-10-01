// The tutorial: highlights its Kanon code with tree-sitter, and fills its
// examples (div.example[data-example]) with their sources and the code that
// Kanon generates from them, computed by the runtime when they come into view.

import "../styles/base.css";
import "./tutorial.css";
import { exampleById, roots, type Example } from "../examples";
import { highlightKanon, loadKanonSyntax, type KanonSyntax } from "../highlight/kanon";
import { highlightStatic, languageOf } from "../highlight/languages";
import { KanonRuntime } from "../runtime/client";
import type { RunResult } from "../runtime/protocol";
import { initTheme } from "../theme";
import { el, escapeHtml } from "../util";

initTheme();

const syntaxReady = loadKanonSyntax();
const runtimeReady = KanonRuntime.load();
runtimeReady.catch((e) => console.error("Kanon runtime:", e));

syntaxReady.then((syntax) => {
  if (!syntax) return;
  for (const pre of document.querySelectorAll<HTMLElement>('pre[data-lang="kanon"]')) {
    pre.innerHTML = highlightKanon(syntax, pre.textContent ?? "");
  }
});

// Runs of kanon, one at a time: the files of an example are written to the
// runtime's root directory while it runs.
let queue: Promise<unknown> = Promise.resolve();
let written: Example | undefined;
const results = new Map<string, Promise<RunResult>>();

function run(ex: Example, backend: string): Promise<RunResult> {
  const key = `${ex.id}:${backend}`;
  let r = results.get(key);
  if (!r) {
    r = queue.then(async () => {
      const rt = await runtimeReady;
      const dir = rt.info.root;
      if (written !== ex) {
        if (written) for (const [name] of written.files) await rt.removeFile(`${dir}/${name}`);
        for (const [name, text] of ex.files) await rt.writeFile(`${dir}/${name}`, text);
        written = ex;
      }
      return rt.run([backend, `${dir}/${roots(ex.files)[0]}`]);
    });
    queue = r.catch(() => {});
    results.set(key, r);
  }
  return r;
}

const OCAML_BACKENDS = ["ocaml", "ocaml-check", "ocaml-tests"];
const LEAN_BACKENDS = [
  "lean-types",
  "lean-syntax",
  "lean-signatures",
  "lean-typing",
  "lean-model",
  "lean-statements",
  "lean-lifts",
  "lean-soundness",
];

function outputPane(ex: Example, title: string, backends: string[], initial: string) {
  const select = el("select", { "aria-label": `${title} backend` });
  const fill = (list: string[]) => {
    const value = select.value || initial;
    select.replaceChildren(...list.map((b) => el("option", { value: b }, b)));
    select.value = list.includes(value) ? value : list[0];
  };
  fill(backends);
  const code = el("pre", { class: "code output-code", "aria-live": "polite" });
  const pane = el("div", { class: "output" }, el("div", { class: "output-head" }, el("span", {}, title), select), code);

  async function show() {
    const backend = select.value;
    code.classList.add("loading");
    code.textContent = "Generating with kanon…";
    try {
      const r = await run(ex, backend);
      if (select.value !== backend) return;
      code.classList.remove("loading");
      if (r.code !== 0) {
        code.innerHTML = `<span class="output-error">${escapeHtml(r.stderr.trim() || `kanon exited with code ${r.code}`)}</span>`;
        if (r.stderr.startsWith("usage:")) code.innerHTML = `<span class="output-note">This backend needs the rules of the language (.kn files).</span>`;
      } else code.innerHTML = highlightStatic(languageOf(backend), r.stdout);
    } catch (e) {
      code.classList.remove("loading");
      code.innerHTML = `<span class="output-error">The Kanon runtime is unavailable: ${escapeHtml(String((e as Error).message ?? e))}</span>`;
    }
  }
  select.addEventListener("change", show);
  runtimeReady.then((rt) => fill(rt.info.backends.filter((b) => backends.includes(b)))).catch(() => {});
  return { pane, show };
}

function mountExample(host: HTMLElement, syntax: Promise<KanonSyntax | null>) {
  const ex = exampleById(host.dataset.example ?? "");
  if (!ex) {
    host.textContent = `Unknown example ${host.dataset.example}`;
    return;
  }
  // the sources, one tab per file
  const source = el("pre", { class: "code example-source" });
  const tabs = el("div", { class: "example-tabs", role: "tablist", "aria-label": "Files" });
  const showFile = async (i: number) => {
    tabs.querySelectorAll("button").forEach((b, j) => b.setAttribute("aria-selected", String(i === j)));
    const text = ex.files[i][1];
    source.textContent = text;
    const s = await syntax;
    if (s && source.textContent === text) source.innerHTML = highlightKanon(s, text);
  };
  ex.files.forEach(([name], i) => {
    const b = el("button", { type: "button", role: "tab", class: "example-tab" }, name);
    b.addEventListener("click", () => showFile(i));
    tabs.append(b);
  });
  showFile(0);

  const open = el("a", { class: "button", href: `sandbox.html#example=${ex.id}` }, "Open in sandbox");
  const ocaml = outputPane(ex, "OCaml", OCAML_BACKENDS, host.dataset.ocaml ?? "ocaml");
  const lean = outputPane(ex, "Lean", LEAN_BACKENDS, host.dataset.lean ?? "lean-model");
  host.replaceChildren(
    el("div", { class: "example-head" }, tabs, open),
    source,
    el("div", { class: "example-generated", "aria-label": "Generated code" }, ocaml.pane, lean.pane),
  );
  for (const p of [ocaml, lean]) p.pane.querySelector("pre")!.textContent = "Loading Kanon…";

  const io = new IntersectionObserver(
    (entries) => {
      if (entries.some((e) => e.isIntersecting)) {
        io.disconnect();
        ocaml.show().then(() => lean.show());
      }
    },
    { rootMargin: "600px 0px" },
  );
  io.observe(host);
}

for (const host of document.querySelectorAll<HTMLElement>("div.example")) mountExample(host, syntaxReady);

// the current section in the table of contents
const links = new Map(
  [...document.querySelectorAll<HTMLAnchorElement>(".toc a")].map((a) => [a.hash.slice(1), a] as const),
);
const sections = new IntersectionObserver(
  (entries) => {
    for (const e of entries)
      if (e.isIntersecting) {
        links.forEach((a) => a.removeAttribute("aria-current"));
        links.get(e.target.id)?.setAttribute("aria-current", "true");
      }
  },
  { rootMargin: "-20% 0px -70% 0px" },
);
document.querySelectorAll("main section[id]").forEach((s) => sections.observe(s));
