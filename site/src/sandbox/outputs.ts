// The outputs panel: the code that a backend generates from a root file of the
// sandbox, regenerated on changes (Auto) or with the button, and the errors of
// kanon, whose locations open the files.

import { Compartment, EditorState } from "@codemirror/state";
import { EditorView } from "@codemirror/view";
import { languageOf, type CodeLanguage } from "../highlight/languages";
import type { KanonRuntime } from "../runtime/client";
import { debounce, el, escapeHtml } from "../util";
import { outputExtensions } from "./editor";

export interface OutputsHost {
  runtime(): KanonRuntime | null;
  /** The names of the root files, in order of preference. */
  roots(): string[];
  /** Writes the pending changes to the runtime's files. */
  flush(): Promise<void>;
  open(file: string, line: number, column: number): void;
  changed(): void;
}

// a location in kanon's errors: lang.knl:20:41 (line from 1, column from 0),
// maybe with the directory of the files
const LOCATION = /((?:\/[^\s:]+\/)?)([\w.+-]+\.knl?):(\d+):(\d+)/g;

export class Outputs {
  readonly backend = document.getElementById("backend") as HTMLSelectElement;
  readonly root = document.getElementById("root") as HTMLSelectElement;
  readonly auto = document.getElementById("auto") as HTMLInputElement;
  private button = document.getElementById("regenerate") as HTMLButtonElement;
  private errors = document.getElementById("output-errors") as HTMLDivElement;
  private language = new Compartment();
  private lang: CodeLanguage = "ocaml";
  private view: EditorView;
  private generation = 0;
  private shown = "";

  constructor(private host: OutputsHost) {
    this.view = new EditorView({
      parent: document.getElementById("output")!,
      state: this.state(""),
    });
    this.backend.addEventListener("change", () => {
      this.host.changed();
      this.generate();
    });
    this.root.addEventListener("change", () => {
      this.host.changed();
      this.generate();
    });
    this.auto.addEventListener("change", () => this.auto.checked && this.generate());
    this.button.addEventListener("click", () => this.generate());
    this.errors.addEventListener("click", (e) => {
      const a = (e.target as HTMLElement).closest<HTMLAnchorElement>("a[data-file]");
      if (!a) return;
      e.preventDefault();
      this.host.open(a.dataset.file!, Number(a.dataset.line), Number(a.dataset.column));
    });
  }

  private state(doc: string) {
    return EditorState.create({ doc, extensions: [this.language.of(outputExtensions(this.lang))] });
  }

  setBackends(backends: string[], preferred?: string) {
    const value = preferred && backends.includes(preferred) ? preferred : this.backend.value || "ocaml";
    this.backend.replaceChildren(...backends.map((b) => el("option", { value: b }, b)));
    this.backend.value = backends.includes(value) ? value : backends[0];
  }

  /** Updates the choice of root files. */
  updateRoots(preferred?: string) {
    const roots = this.host.roots();
    const value = preferred ?? this.root.value;
    const same = [...this.root.options].map((o) => o.value).join("\n") === roots.join("\n");
    if (!same) this.root.replaceChildren(...roots.map((r) => el("option", { value: r }, r)));
    this.root.value = roots.includes(value) ? value : (roots[0] ?? "");
    this.root.disabled = roots.length === 0;
  }

  /** Regenerates, if Auto is on, after a pause. */
  readonly changedFiles = debounce(() => {
    if (this.auto.checked) this.generate();
  }, 500);

  async generate() {
    const rt = this.host.runtime();
    if (!rt) return;
    this.updateRoots();
    const backend = this.backend.value;
    const root = this.root.value;
    const gen = ++this.generation;
    if (!root) {
      this.show("", "No root file: add a .knl file that no other file uses.");
      return;
    }
    this.button.disabled = true;
    this.button.textContent = "Generating…";
    try {
      await this.host.flush();
      const r = await rt.run([backend, `${rt.info.root}/${root}`]);
      if (gen !== this.generation) return;
      const lang = languageOf(backend);
      if (lang !== this.lang) {
        this.lang = lang;
        this.view.dispatch({ effects: this.language.reconfigure(outputExtensions(lang)) });
      }
      this.show(r.stdout, r.code === 0 ? "" : r.stderr.trim() || `kanon exited with code ${r.code}`, `${backend}:${root}`);
    } catch (e) {
      this.show("", `The Kanon runtime failed: ${(e as Error).message}`);
    } finally {
      if (gen === this.generation) {
        this.button.disabled = false;
        this.button.textContent = "Generate";
      }
    }
  }

  private show(stdout: string, stderr: string, key = "") {
    if (stderr) {
      const html = escapeHtml(stderr).replace(
        LOCATION,
        (m, _dir, file, line, column) =>
          `<a href="#" data-file="${file}" data-line="${line}" data-column="${column}">${m}</a>`,
      );
      this.errors.innerHTML = `<pre>${html}</pre>`;
      this.errors.hidden = false;
    } else this.errors.hidden = true;
    // on an error, the last output stays, dimmed
    this.view.dom.classList.toggle("stale", !!stderr);
    if (!stdout && stderr) return;
    const scroll = key === this.shown ? this.view.scrollDOM.scrollTop : 0;
    this.view.dispatch({ changes: { from: 0, to: this.view.state.doc.length, insert: stdout } });
    this.view.scrollDOM.scrollTop = scroll;
    this.shown = key;
  }
}
