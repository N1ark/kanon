<script lang="ts">
  // The sandbox: the files of a language in an editor with Kanon's language server, its problems,
  // and the code that Kanon generates from it.
  import { EditorView } from "@codemirror/view";
  import {
    Banner,
    Button,
    ContextMenuHost,
    DialogHost,
    Kbd,
    ResizeEdge,
    Spinner,
    Tag,
    ToastHost,
    confirmAction,
    copyText,
    dialog,
    menu,
    persisted,
    toast,
  } from "purr";
  import { BookOpen, CaretDown, ListBullets, ShareNetwork } from "purr/icons";
  import Header from "../components/Header.svelte";
  import { exampleById, examples } from "../examples";
  import type { KanonSyntax } from "../highlight/kanon";
  import BottomPanel from "./BottomPanel.svelte";
  import FileTabs from "./FileTabs.svelte";
  import Outputs from "./Outputs.svelte";
  import * as persist from "./persist";
  import { Workspace } from "./workspace.svelte";

  interface Props {
    syntax: KanonSyntax | null;
  }

  const { syntax }: Props = $props();

  // svelte-ignore state_referenced_locally
  const ws = new Workspace(syntax);
  // for the console, and scripts/screenshots.mjs
  (window as any).sandbox = ws;

  const editorWidth = persisted("kanon.sandbox.editor-width", 0, (v): v is number => typeof v === "number");
  const panelHeight = persisted("kanon.sandbox.panel-height", 170, (v): v is number => typeof v === "number");
  let main = $state<HTMLElement | null>(null);
  let editor = $state<HTMLElement | null>(null);
  const width = $derived(editorWidth.value || (main ? main.clientWidth / 2 : 600));

  /** The files to start with: shared in the URL, an example named there, the saved ones, or the tiny language. */
  async function initial(): Promise<{ files: persist.Files; saved: persist.Saved | null }> {
    const hash = new URLSearchParams(location.hash.slice(1));
    if (hash.size) history.replaceState(null, "", location.pathname + location.search);
    const code = hash.get("code");
    if (code) {
      try {
        return { files: await persist.decode(code), saved: null };
      } catch (e) {
        toast(`Could not read the shared files: ${(e as Error).message}`, { kind: "error" });
      }
    }
    const ex = exampleById(hash.get("example") ?? "");
    if (ex) return { files: ex.files, saved: null };
    const saved = persist.load();
    if (saved) return { files: saved.files, saved };
    return { files: exampleById("tiny")!.files, saved: null };
  }

  $effect(() => {
    if (!editor) return;
    const view = new EditorView({ parent: editor });
    initial().then(({ files, saved }) => ws.start(view, files, saved));
    return () => view.destroy();
  });

  function templates(e: MouseEvent & { currentTarget: HTMLElement }) {
    const item = (ex: (typeof examples)[number]) => ({
      label: ex.title,
      note: ex.description,
      run: async () => {
        const sure = await confirmAction(`Replace the files with “${ex.title}”?`, {
          description: "The files of the sandbox are replaced; share them first to keep them.",
          confirmLabel: "Replace",
        });
        if (sure) {
          await ws.load(ex.files);
          ws.saveLater();
        }
      },
    });
    menu.showFor(e.currentTarget, [
      { kind: "heading", label: "Templates" },
      ...examples.filter((x) => x.template).map(item),
      "separator",
      { kind: "heading", label: "Tutorial" },
      ...examples.filter((x) => !x.template).map(item),
    ]);
  }

  async function outline(e: MouseEvent & { currentTarget: HTMLElement }) {
    const anchor = e.currentTarget;
    const symbols = await ws.symbols();
    const f = ws.active;
    if (!f) return;
    menu.showFor(
      anchor,
      symbols.length
        ? symbols.map((s) => ({
            label: " ".repeat(s.depth) + s.name,
            note: s.depth ? undefined : s.detail,
            run: () => ws.openLocation({ uri: ws.uriOf(f), range: s.range }),
          }))
        : [{ label: "No symbols", disabled: true }],
      `Outline of ${f.name}`,
    );
  }

  async function share() {
    const url = await ws.shareUrl();
    if (await copyText(url)) {
      toast("Link copied: it holds the files", { kind: "success" });
      return;
    }
    await dialog.ask({
      title: "Share these files",
      description: "Copy this link: it holds the files.",
      fields: [{ name: "url", label: "Link", value: url }],
      confirmLabel: "Done",
    });
  }
</script>

<ContextMenuHost />
<DialogHost />
<ToastHost />

<div class="app">
  <Header page="sandbox">
    {#if ws.status === "loading"}
      <Spinner size="1em" label="Loading Kanon" /><span class="muted">Loading Kanon…</span>
    {:else if ws.status === "ready" && ws.info}
      {#if ws.info.version === "mock"}
        <Tag label="mock runtime" color="var(--warn)" title="Canned answers: see site/mock/" />
      {:else}
        <Tag label="kanon {ws.info.version}" />
      {/if}
    {/if}
  </Header>

  {#if ws.status === "failed"}
    <Banner
      placement="inline"
      tone="danger"
      title="The Kanon runtime is unavailable"
      lines={[ws.error, "The editor still works, without checks or generated code."]}
    />
  {/if}

  <main class="panes" bind:this={main}>
    <section class="pane editor-pane" style:width="{width}px" aria-label="Editor">
      <FileTabs {ws} />
      <div class="toolbar">
        <Button
          size="sm"
          variant="ghost"
          aria-haspopup="menu"
          disabled={!ws.has("documentSymbolProvider")}
          onclick={outline}><ListBullets /> Outline</Button
        >
        <span class="hints muted">
          <Kbd hint="F12" /> definition
          {#if ws.has("referencesProvider")}· <Kbd hint="⇧F12" /> references{/if}
          {#if ws.has("renameProvider")}· <Kbd hint="F2" /> rename{/if}
        </span>
        <span class="spacer"></span>
        <Button size="sm" aria-haspopup="menu" onclick={templates}><BookOpen /> Templates <CaretDown /></Button>
        <Button size="sm" onclick={share}><ShareNetwork /> Share</Button>
      </div>
      <div class="editor" bind:this={editor}></div>
      <div class="bottom" style:height="{panelHeight.value}px">
        <BottomPanel {ws} />
        <ResizeEdge
          side="bottom"
          label="Resize the problems"
          size={panelHeight.value}
          min={60}
          max={600}
          preset={170}
          onresize={(h) => (panelHeight.value = h)}
        />
      </div>
      <ResizeEdge
        side="left"
        label="Resize the editor"
        size={width}
        min={320}
        max={main ? main.clientWidth - 280 : 2000}
        onresize={(w) => (editorWidth.value = w)}
      />
    </section>
    <section class="pane output-pane">
      <Outputs {ws} />
    </section>
  </main>
</div>

<style>
  .app {
    display: flex;
    flex-direction: column;
    height: 100%;
  }
  .panes {
    display: flex;
    flex: 1;
    min-height: 0;
  }
  .pane {
    position: relative;
    display: flex;
    flex-direction: column;
    min-width: 0;
    min-height: 0;
  }
  .editor-pane {
    flex: none;
    border-right: 1px solid var(--border);
  }
  .output-pane {
    flex: 1;
  }
  .toolbar {
    display: flex;
    align-items: center;
    gap: var(--gap-4);
    padding: var(--sp-2) var(--sp-3);
    border-bottom: 1px solid var(--border);
  }
  .hints {
    font-size: var(--fs-xs);
    white-space: nowrap;
    overflow: hidden;
  }
  .spacer {
    flex: 1;
  }
  .editor {
    flex: 1;
    min-height: 0;
  }
  .editor :global(.cm-editor) {
    height: 100%;
  }
  .bottom {
    position: relative;
    flex: none;
    border-top: 1px solid var(--border);
  }
  @media (max-width: 900px) {
    .panes {
      flex-direction: column;
    }
    .editor-pane {
      width: auto !important;
      height: 60%;
      border-right: none;
      border-bottom: 1px solid var(--border);
    }
    .editor-pane > :global(.edge-left),
    .hints {
      display: none;
    }
    .bottom {
      height: 6rem !important;
    }
  }
</style>
