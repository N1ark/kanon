import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { dirname, extname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { svelte } from "@sveltejs/vite-plugin-svelte";
import { purr } from "purr/vite";
import { defineConfig, type Plugin } from "vite";

const site = dirname(fileURLToPath(import.meta.url));
const repo = resolve(site, "..");

/** The web runtime of Kanon, served and copied at kanon/: the output of
 * `dune build @web` (or $KANON_WEB_DIST), or the mock of mock/ with
 * KANON_MOCK=1. In development, the mock stands in for a missing runtime. */
function kanonRuntime(): Plugin {
  const dist = resolve(site, process.env.KANON_WEB_DIST ?? join(repo, "_build/default/web/dist"));
  let mock = process.env.KANON_MOCK === "1";

  function files(): Map<string, Buffer | string> {
    const out = new Map<string, Buffer | string>();
    if (mock) {
      const builtins = Object.fromEntries(
        readdirSync(join(repo, "modules")).map((f) => [f, readFileSync(join(repo, "modules", f), "utf8")]),
      );
      const fixtures = JSON.parse(readFileSync(join(site, "mock/fixtures.json"), "utf8"));
      out.set(
        "kanon.js",
        `var KANON_MOCK_DATA = ${JSON.stringify({ builtins, fixtures })};\n` +
          readFileSync(join(site, "mock/kanon.js"), "utf8"),
      );
      return out;
    }
    const walk = (dir: string) => {
      for (const f of readdirSync(dir)) {
        const p = join(dir, f);
        if (statSync(p).isDirectory()) walk(p);
        else out.set(relative(dist, p).split(sep).join("/"), readFileSync(p));
      }
    };
    walk(dist);
    return out;
  }

  const types: Record<string, string> = {
    ".js": "text/javascript",
    ".wasm": "application/wasm",
    ".json": "application/json",
    ".map": "application/json",
  };

  return {
    name: "kanon-runtime",
    configResolved(config) {
      if (mock || config.command !== "build" || existsSync(join(dist, "kanon.js"))) return;
      throw new Error(
        `No Kanon runtime in ${dist}: build it (dune build @web --profile web at the root of the ` +
          "repository), set KANON_WEB_DIST to its directory, or build with the mock runtime (KANON_MOCK=1).",
      );
    },
    configureServer(server) {
      if (!mock && !existsSync(join(dist, "kanon.js"))) {
        server.config.logger.warn(`kanon-runtime: no runtime in ${dist}, serving the mock runtime instead`);
        mock = true;
      }
      server.middlewares.use((req, res, next) => {
        const url = (req.url ?? "").split("?")[0];
        const m = /^\/kanon\/(.+)$/.exec(url);
        if (!m) return next();
        const f = files().get(decodeURIComponent(m[1]));
        if (f === undefined) return next();
        res.setHeader("Content-Type", types[extname(m[1])] ?? "application/octet-stream");
        res.setHeader("Cache-Control", "no-store");
        res.end(f);
      });
    },
    generateBundle() {
      for (const [fileName, source] of files()) this.emitFile({ type: "asset", fileName: `kanon/${fileName}`, source });
    },
  };
}

/** The tree-sitter grammar, built by `npm run grammar` into public/. */
function grammarCheck(): Plugin {
  return {
    name: "kanon-grammar",
    configResolved(config) {
      if (existsSync(join(site, "public/tree-sitter-kanon.wasm"))) return;
      const message = "public/tree-sitter-kanon.wasm is missing: build it with `npm run grammar` (see README.md)";
      if (config.command === "build") throw new Error(message);
      config.logger.warn(`kanon-grammar: ${message}; Kanon is shown without highlighting`);
    },
  };
}

export default defineConfig({
  base: "./",
  plugins: [purr({ weights: ["regular", "bold", "fill"] }), svelte(), kanonRuntime(), grammarCheck()],
  // the examples and the highlighting queries are imported from the repository
  server: { fs: { allow: [repo] } },
  worker: { format: "iife" },
  build: {
    target: "es2022",
    // CodeMirror, tree-sitter and purr, shared by the pages
    chunkSizeWarningLimit: 1200,
    rollupOptions: {
      input: {
        index: join(site, "index.html"),
        proving: join(site, "proving.html"),
        reference: join(site, "reference.html"),
        sandbox: join(site, "sandbox.html"),
      },
    },
  },
});
