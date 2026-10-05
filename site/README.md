# The Kanon site

A tutorial of Kanon, a guide to its proofs, its reference and a sandbox to try
it, in the browser, published at <https://n1ark.github.io/kanon/>:

- `index.html`, the tutorial: a tiny language built step by step, with the
  OCaml and the Lean that Kanon generates from each step, computed in the
  page;
- `proving.html`, the guide to proofs: how to prove a language in Lean, on
  the example `examples/ints/` of the repository, whose files it quotes;
- `reference.html`, the reference: the declarations, the attributes and the
  operators, the rules, the generated code and the language server;
- `sandbox.html`, the sandbox: the files of a language in an editor with
  Kanon's language server (diagnostics, hovers, completion, definitions,
  references, rename, outline), and the output of every backend. The files are
  saved in the browser, and Share puts them in a link.

The tutorial and the sandbox run Kanon itself: its web runtime (`web/` in the repository: the checker,
the generators and the language server, compiled with js_of_ocaml) in a Web
Worker. Kanon is highlighted by its tree-sitter grammar (`tree-sitter-kanon/`)
with the highlighting query of the Zed extension
(`editors/zed/languages/kanon/highlights.scm`). The interface is Svelte 5 with
[purr](https://github.com/N1ark/purr)'s components and styling; the editors are
CodeMirror 6.

## Running it locally

From the root of the repository, with OCaml (see the main README), Node.js ≥
22.18, and emscripten or docker:

```sh
# the web runtime, in _build/default/web/dist/kanon.js
opam install js_of_ocaml-compiler js_of_ocaml zarith_stubs_js
dune build @web --profile web

cd site
npm install
# the grammar, in public/tree-sitter-kanon.wasm: with emcc in PATH (or
# EMSDK=path/to/an/activated/emsdk), or else in docker
npm run grammar
npm run dev        # http://localhost:5173
```

`npm run build` checks the code (svelte-check) and builds the site into
`dist/`, with relative URLs, so that it can be served from any directory. The
runtime is copied into `dist/kanon/`.

### The runtime, or its mock

The pages load the runtime from `kanon/kanon.js`, next to them. `vite.config.ts`
serves and copies it from `../_build/default/web/dist/`, or from
`$KANON_WEB_DIST`. With `KANON_MOCK=1` (`npm run dev:mock`, `npm run
build:mock`), it is `mock/kanon.js` instead: the same API with canned answers,
for working on the site without OCaml. Its outputs, in `mock/fixtures.json`,
are those of a native kanon on the examples (`KANON=path/to/kanon npm run
mock-fixtures`); its language server only imitates the real one. The dev
server falls back on the mock when there is no runtime.

### Examples

`examples/index.json` lists the examples, the templates of the sandbox and the
steps of the tutorial. Their files are imported at build time: the templates
from the repository (`examples/bool/`, `modules/`, `test/tiny.t/`), the steps
from `examples/` here, but the last one, which is `examples/ints/` of the
repository (whose Lean proof the guide quotes).

### Checking it in a browser

```sh
npm run build      # or build:mock
CHROMIUM=path/to/chrome npm run shots -- OUT_DIR
```

opens the built site in headless Chromium, checks that it works (no errors in
the console, tree-sitter highlighting, generated code, diagnostics, hovers,
completion, a definition in the built-in module, a shared link) and takes
screenshots of the tutorial, the guide, the reference and the sandbox, in
light and dark.

## Deployment

`.github/workflows/pages.yml` builds the runtime, the grammar and the site on
every pull request, where the site is an artifact of the run (`site`, to
download), and deploys it to GitHub Pages on every push to `main` (or by
hand). The repository's Pages must be set once to deploy from GitHub Actions:
Settings → Pages → Build and deployment → Source: GitHub Actions.
