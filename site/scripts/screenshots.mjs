// Checks the built site (dist/) in a headless Chromium, and takes screenshots
// of the tutorial, the reference and the sandbox, in light and dark: no errors
// in the console, Kanon highlighted by tree-sitter, the generated code shown,
// and in the sandbox a diagnostic, a hover and the outputs.
//
//   npm run build:mock && npm run shots -- OUT_DIR
//
// $CHROMIUM is the browser (playwright-core does not download one).

import { mkdirSync } from "node:fs";
import { join } from "node:path";
import { chromium } from "playwright-core";
import { preview } from "vite";

const out = process.argv[2] ?? "screenshots";
mkdirSync(out, { recursive: true });

const server = await preview({ preview: { port: 4179, strictPort: false }, logLevel: "warn" });
const base = server.resolvedUrls.local[0];
const browser = await chromium.launch({ executablePath: process.env.CHROMIUM });
const problems = [];
const shots = [];

async function page(colorScheme, width = 1440, height = 900) {
  const context = await browser.newContext({ colorScheme, viewport: { width, height }, deviceScaleFactor: 1 });
  const p = await context.newPage();
  p.on("console", (m) => {
    if (m.type() === "error" || m.type() === "warning") problems.push(`[${colorScheme}] console.${m.type()}: ${m.text()}`);
  });
  p.on("pageerror", (e) => problems.push(`[${colorScheme}] page error: ${e.message}`));
  return p;
}

async function shot(p, name, target) {
  const path = join(out, `${name}.png`);
  if (target) await target.screenshot({ path });
  else await p.screenshot({ path });
  shots.push(path);
}

function check(cond, what) {
  if (!cond) problems.push(`check failed: ${what}`);
  console.log(`${cond ? "ok  " : "FAIL"} ${what}`);
}

for (const scheme of ["light", "dark"]) {
  // the tutorial
  const t = await page(scheme);
  await t.goto(base);
  await t.waitForSelector('pre[data-lang="kanon"] span.ts-keyword');
  const spans = await t.$$eval('pre[data-lang="kanon"] span[class^="ts-"]', (s) => s.length);
  check(spans > 50, `${scheme}: tutorial code highlighted by tree-sitter (${spans} capture spans)`);
  await shot(t, `tutorial-top-${scheme}`);
  const ex = t.locator('figure[data-example="rules"]');
  await ex.scrollIntoViewIfNeeded();
  await t.waitForFunction(
    () => [...document.querySelectorAll('figure[data-example="rules"] section pre')].filter((e) => e.textContent.length > 100).length === 2,
    null,
    { timeout: 30000 },
  );
  const ocaml = await ex.locator("section[aria-label=OCaml] pre").textContent();
  check(ocaml.includes("let rec plus"), `${scheme}: tutorial example shows the generated OCaml`);
  // below the sticky header
  await ex.evaluate((e) => window.scrollTo(0, e.getBoundingClientRect().top + window.scrollY - 60));
  await shot(t, `tutorial-example-${scheme}`);
  await t.close();

  // the tutorial on a phone
  if (scheme === "light") {
    const m = await page(scheme, 390, 844);
    await m.goto(base);
    await m.waitForSelector('pre[data-lang="kanon"] span.ts-keyword');
    await shot(m, `tutorial-phone-${scheme}`);
    await m.close();
  }

  // the reference
  const r = await page(scheme);
  await r.goto(`${base}reference.html`);
  await r.waitForSelector('pre[data-lang="kanon"] span.ts-keyword');
  const rows = await r.$$eval("table tr", (x) => x.length);
  check(rows > 30, `${scheme}: reference tables (${rows} rows)`);
  await shot(r, `reference-top-${scheme}`);
  await r.locator("#operators").scrollIntoViewIfNeeded();
  await shot(r, `reference-operators-${scheme}`);
  await r.close();

  // the sandbox, with the tiny language
  const s = await page(scheme);
  await s.goto(`${base}sandbox.html#example=tiny`);
  await s.waitForFunction(() => window.sandbox?.status === "ready", null, { timeout: 30000 });
  await s.waitForSelector(".editor .cm-content span.ts-keyword");
  const cmSpans = await s.$$eval('.editor .cm-content span[class^="ts-"]', (x) => x.length);
  check(cmSpans > 20, `${scheme}: editor highlighted by tree-sitter (${cmSpans} capture spans)`);
  await s.waitForFunction(() => document.querySelector(".outputs .cm-content")?.textContent.includes("let"), null, { timeout: 30000 });
  check(true, `${scheme}: outputs panel shows the generated code`);

  // a diagnostic: an unknown node in rules.kn
  await s.getByRole("tab", { name: "rules.kn", exact: true }).click();
  await s.locator(".editor .cm-content").click();
  await s.evaluate(() => {
    const view = window.sandbox.view;
    const text = view.state.doc.toString();
    const at = text.indexOf("Plus (v1, v2)");
    view.dispatch({ changes: { from: at, to: at + 4, insert: "Plu" } });
  });
  await s.waitForSelector(".editor .cm-lintRange-error", { timeout: 10000 });
  const nProblems = await s.locator(".panel button.row-item").count();
  check(nProblems > 0, `${scheme}: the problems panel lists the diagnostic`);
  await s.waitForSelector(".outputs .errors", { timeout: 10000 });
  await shot(s, `sandbox-diagnostic-${scheme}`);

  // fix it, and hover a helper
  await s.evaluate(() => {
    const view = window.sandbox.view;
    const text = view.state.doc.toString();
    const at = text.indexOf("Plu (v1, v2)");
    view.dispatch({ changes: { from: at, to: at + 3, insert: "Plus" } });
  });
  await s.waitForFunction(() => !document.querySelector(".editor .cm-lintRange-error"), null, { timeout: 10000 });
  const target = s.locator(".editor .cm-line", { hasText: "-> of_bool (x = y)" }).locator("span", { hasText: /^of_bool$/ });
  await target.hover();
  await s.waitForSelector(".cm-lsp-hover", { timeout: 10000 });
  const hoverSpans = await s.$$eval(".cm-lsp-hover span[class^='ts-']", (x) => x.length);
  check(hoverSpans > 0, `${scheme}: hover rendered, with highlighted Kanon (${hoverSpans} spans)`);
  await shot(s, `sandbox-hover-${scheme}`);

  // the Lean model
  await s.getByRole("button", { name: /Backend/ }).click();
  await s.locator("[role^=menuitem]", { hasText: "lean-model" }).click();
  await s.waitForFunction(() => document.querySelector(".outputs .cm-content")?.textContent.includes("def "), null, { timeout: 10000 });
  await s.mouse.move(5, 5);
  await shot(s, `sandbox-lean-${scheme}`);
  await s.close();
}

// the rest of the sandbox, once: completion, a definition in a built-in module, sharing
{
  const s = await page("light");
  await s.goto(`${base}sandbox.html#example=modules`);
  await s.waitForFunction(() => window.sandbox?.status === "ready", null, { timeout: 30000 });
  await s.getByRole("tab", { name: "int.kn", exact: true }).click();
  // hover on an operator
  await s.locator(".editor .cm-line", { hasText: "lits: #x lt #y" }).locator("span", { hasText: /^lt$/ }).first().hover();
  await s.waitForSelector(".cm-lsp-hover", { timeout: 10000 });
  const opHover = await s.locator(".cm-lsp-hover").textContent();
  check(/Lt|int_lt/.test(opHover), `hover on lt shows its operator (${opHover.replace(/\s+/g, " ").slice(0, 60)}…)`);
  await shot(s, "sandbox-hover-operator-light");
  await s.mouse.move(5, 5);
  // references of of_bool, if the server finds them
  const refs = await s.evaluate(() => window.sandbox.has("referencesProvider"));
  if (refs) {
    await s.evaluate(() => {
      const view = window.sandbox.view;
      view.dispatch({ selection: { anchor: view.state.doc.toString().indexOf("of_bool") + 2 } });
      view.focus();
    });
    await s.keyboard.press("Shift+F12");
    await s.waitForFunction(() => window.sandbox.references?.length > 0, null, { timeout: 10000 });
    check(true, "Shift+F12 lists the references");
    await shot(s, "sandbox-references-light");
  }
  // completion at the end of the file
  await s.evaluate(() => {
    const view = window.sandbox.view;
    view.dispatch({ changes: { from: view.state.doc.length, insert: "\nfn f (x : t) : t = of_b" }, selection: { anchor: view.state.doc.length + 23 } });
    view.focus();
  });
  await s.keyboard.press("Control+Space");
  await s.waitForSelector(".cm-tooltip-autocomplete li", { timeout: 10000 });
  const options = await s.$$eval(".cm-tooltip-autocomplete li", (x) => x.map((l) => l.textContent));
  check(options.some((o) => o.includes("of_bool")), `completion offers of_bool (${options.slice(0, 3).join(", ")}…)`);
  await shot(s, "sandbox-completion-light");
  await s.keyboard.press("Escape");
  // F12 on of_bool, defined in the built-in bool module
  await s.evaluate(() => {
    const view = window.sandbox.view;
    const at = view.state.doc.toString().indexOf("of_bool (x < y)");
    view.dispatch({ selection: { anchor: at + 2 } });
    view.focus();
  });
  await s.keyboard.press("F12");
  await s.waitForFunction(() => window.sandbox.active?.builtinPath, null, { timeout: 10000 });
  const opened = await s.evaluate(() => window.sandbox.active.name);
  check(opened === "bool.kn", `F12 opens the built-in ${opened}, read-only`);
  await shot(s, "sandbox-definition-light");
  // a link that holds the files opens them
  const url = await s.evaluate(() => window.sandbox.shareUrl());
  const t = await page("light");
  await t.goto(url);
  await t.waitForFunction(() => window.sandbox?.files.length, null, { timeout: 30000 });
  const names = await t.evaluate(() => window.sandbox.files.map((f) => f.name).join(" "));
  check(names === "lang.knl int.knl int.kn", `a shared link opens its files (${names})`);
  await t.close();
  await s.close();
}

await browser.close();
server.httpServer.close();
console.log("\nscreenshots:\n" + shots.join("\n"));
if (problems.length) {
  console.log("\nproblems:\n" + problems.join("\n"));
  process.exitCode = 1;
}
