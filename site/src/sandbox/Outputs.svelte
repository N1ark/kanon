<script lang="ts">
  // The code that a backend generates from a root file, in a read-only editor: regenerated after
  // each check of the files (Auto) or with the button. kanon's errors link to their locations;
  // on an error the last output stays, dimmed.
  import { Compartment, EditorState } from "@codemirror/state";
  import { EditorView } from "@codemirror/view";
  import { Button, Switch, menu } from "purr";
  import { untrack } from "svelte";
  import { CaretDown, Play } from "purr/icons";
  import { languageOf, type CodeLanguage } from "../highlight/languages";
  import { escapeHtml } from "../lib/util";
  import { outputExtensions } from "./editor";
  import type { Workspace } from "./workspace.svelte";

  interface Props {
    ws: Workspace;
  }

  const { ws }: Props = $props();

  let backend = $state(untrack(() => ws.outputChoice.backend) ?? "ocaml");
  let root = $state(untrack(() => ws.outputChoice.root) ?? "");
  let auto = $state(true);
  let running = $state(false);
  let errors = $state("");
  let stale = $state(false);

  const backends = $derived(ws.info?.backends ?? []);
  const roots = $derived.by(() => {
    void ws.revision;
    void ws.files;
    return ws.roots();
  });
  const chosenRoot = $derived(roots.includes(root) ? root : (roots[0] ?? ""));

  let host = $state<HTMLElement | null>(null);
  let view: EditorView | null = null;
  const language = new Compartment();
  let lang: CodeLanguage = "ocaml";
  let shown = "";
  let generation = 0;

  $effect(() => {
    if (!host) return;
    view = new EditorView({
      parent: host,
      state: EditorState.create({ extensions: [language.of(outputExtensions(lang))] }),
    });
    return () => view?.destroy();
  });

  // remembered with the files
  $effect(() => {
    ws.outputChoice = { backend, root: chosenRoot || undefined };
    ws.saveLater();
  });

  // after each check when Auto is on, and on a new choice of backend or root
  let lastChoice = "";
  $effect(() => {
    void ws.revision;
    const choice = `${backend}:${chosenRoot}`;
    if (ws.status !== "ready") return;
    const chosen = choice !== lastChoice;
    lastChoice = choice;
    if (auto || chosen) untrack(generate);
  });

  async function generate() {
    const rt = ws.runtime;
    if (!rt || !view) return;
    const b = backend;
    const r0 = chosenRoot;
    const gen = ++generation;
    if (!r0) {
      show("", "No root file: add a .knl file that no other file uses.", "");
      return;
    }
    running = true;
    try {
      await ws.flush();
      const r = await rt.run([b, `${rt.info.root}/${r0}`]);
      if (gen !== generation) return;
      const l = languageOf(b);
      if (l !== lang) {
        lang = l;
        view.dispatch({ effects: language.reconfigure(outputExtensions(l)) });
      }
      show(r.stdout, r.code === 0 ? "" : r.stderr.trim() || `kanon exited with code ${r.code}`, `${b}:${r0}`);
    } catch (e) {
      show("", `The Kanon runtime failed: ${(e as Error).message}`, "");
    } finally {
      if (gen === generation) running = false;
    }
  }

  function show(stdout: string, stderr: string, key: string) {
    errors = stderr;
    stale = !!stderr;
    if (!view || (!stdout && stderr)) return;
    const scroll = key === shown ? view.scrollDOM.scrollTop : 0;
    view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: stdout } });
    view.scrollDOM.scrollTop = scroll;
    shown = key;
  }

  // lang.knl:20:41, maybe after the directory of the files: line from 1, column from 0
  const LOCATION = /((?:\/[^\s:]+\/)?)([\w.+-]+\.knl?):(\d+):(\d+)/g;
  const errorsHtml = $derived(
    escapeHtml(errors).replace(
      LOCATION,
      (m, _dir, file, line, column) =>
        `<a href="#${file}:${line}:${column}" data-file="${file}" data-line="${line}" data-column="${column}">${m}</a>`,
    ),
  );

  function openError(e: MouseEvent) {
    const a = (e.target as HTMLElement).closest<HTMLAnchorElement>("a[data-file]");
    if (!a) return;
    e.preventDefault();
    ws.openFileAt(a.dataset.file!, Number(a.dataset.line), Number(a.dataset.column));
  }

  function pick(e: MouseEvent & { currentTarget: HTMLElement }, title: string, list: string[], current: string, set: (v: string) => void) {
    menu.showFor(
      e.currentTarget,
      list.map((v) => ({ label: v, checked: v === current, run: () => set(v) })),
      title,
    );
  }

  function pickBackend(e: MouseEvent & { currentTarget: HTMLElement }) {
    const group = (prefix: string) =>
      backends.filter((b) => b.startsWith(prefix)).map((b) => ({ label: b, checked: b === backend, run: () => (backend = b) }));
    menu.showFor(e.currentTarget, [
      { kind: "heading", label: "OCaml" },
      ...group("ocaml"),
      "separator",
      { kind: "heading", label: "Lean" },
      ...group("lean"),
    ]);
  }
</script>

<section class="outputs" aria-label="Generated code">
  <div class="toolbar">
    <Button size="sm" aria-haspopup="menu" disabled={!backends.length} onclick={pickBackend}>
      <span class="muted">Backend</span> <span class="mono">{backend}</span> <CaretDown />
    </Button>
    <Button
      size="sm"
      aria-haspopup="menu"
      disabled={roots.length < 2}
      onclick={(e) => pick(e, "Root file", roots, chosenRoot, (v) => (root = v))}
    >
      <span class="muted">Root</span> <span class="mono">{chosenRoot || "none"}</span>
      {#if roots.length > 1}<CaretDown />{/if}
    </Button>
    <span class="spacer"></span>
    <label class="auto">
      <Switch label="Regenerate on changes" bind:checked={auto} />
      <span class="muted">Auto</span>
    </label>
    <Button
      size="sm"
      variant="primary"
      loading={running}
      loadingLabel="Generating"
      disabled={!ws.runtime}
      onclick={generate}><Play weight="fill" /> Generate</Button
    >
  </div>
  {#if errors}
    <!-- the links in it are the interactive part -->
    <!-- svelte-ignore a11y_no_noninteractive_element_interactions, a11y_click_events_have_key_events -->
    <div class="errors" role="alert" onclick={openError}><pre>{@html errorsHtml}</pre></div>
  {/if}
  <div class="code" class:stale bind:this={host}></div>
</section>

<style>
  .outputs {
    display: flex;
    flex-direction: column;
    min-width: 0;
    min-height: 0;
    height: 100%;
  }
  .toolbar {
    display: flex;
    align-items: center;
    flex-wrap: wrap;
    gap: var(--gap-4);
    padding: var(--sp-2) var(--sp-3);
    border-bottom: 1px solid var(--border);
    background: var(--bg2);
  }
  .spacer {
    flex: 1;
  }
  .auto {
    display: inline-flex;
    align-items: center;
    gap: var(--gap-3);
    font-size: var(--fs-sm);
  }
  .errors {
    max-height: 40%;
    overflow: auto;
    border-bottom: 1px solid var(--border);
    background: color-mix(in srgb, var(--danger) 9%, var(--bg));
  }
  .errors pre {
    margin: 0;
    padding: var(--sp-3) var(--sp-4);
    font-family: var(--mono);
    font-size: var(--fs-sm);
    white-space: pre-wrap;
    color: var(--danger);
  }
  .errors :global(a) {
    color: inherit;
    font-weight: 600;
    text-decoration: underline;
  }
  .code {
    flex: 1;
    min-height: 0;
  }
  .code :global(.cm-editor) {
    height: 100%;
  }
  .code.stale {
    opacity: 0.55;
  }
</style>
