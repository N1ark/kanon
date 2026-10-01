// Checks the built site (dist/) in a headless Chromium, and takes screenshots
// of the tutorial and of the sandbox, in light and dark: no errors in the
// console, Kanon highlighted by tree-sitter, the generated code shown, and in
// the sandbox a diagnostic, a hover and the outputs.
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
  const ex = t.locator('.example[data-example="rules"]');
  await ex.scrollIntoViewIfNeeded();
  await t.waitForFunction(
    () => [...document.querySelectorAll('.example[data-example="rules"] .output-code')].every((e) => !e.classList.contains("loading") && e.textContent.length > 100),
    null,
    { timeout: 30000 },
  );
  const ocaml = await ex.locator(".output-code").first().textContent();
  check(ocaml.includes("let rec plus"), `${scheme}: tutorial example shows the generated OCaml`);
  await shot(t, `tutorial-example-${scheme}`, ex);
  await t.close();

  // the tutorial on a phone
  if (scheme === "light") {
    const m = await page(scheme, 390, 844);
    await m.goto(base);
    await m.waitForSelector('pre[data-lang="kanon"] span.ts-keyword');
    await shot(m, `tutorial-phone-${scheme}`);
    await m.close();
  }

  // the sandbox, with the tiny language
  const s = await page(scheme);
  await s.goto(`${base}sandbox.html#example=tiny`);
  await s.waitForFunction(() => /kanon/.test(document.getElementById("status").textContent), null, { timeout: 30000 });
  await s.waitForSelector(".editor .cm-content span.ts-keyword");
  const cmSpans = await s.$$eval('.editor .cm-content span[class^="ts-"]', (x) => x.length);
  check(cmSpans > 20, `${scheme}: editor highlighted by tree-sitter (${cmSpans} capture spans)`);
  await s.waitForFunction(() => document.querySelector("#output .cm-content")?.textContent.includes("let"), null, { timeout: 30000 });
  check(true, `${scheme}: outputs panel shows the generated code`);

  // a diagnostic: an unknown node in rules.kn
  await s.locator(".tab", { hasText: "rules.kn" }).click();
  await s.locator(".editor .cm-content").click();
  await s.evaluate(() => {
    const view = window.sandbox.view;
    const text = view.state.doc.toString();
    const at = text.indexOf("Plus (v1, v2)");
    view.dispatch({ changes: { from: at, to: at + 4, insert: "Plu" } });
  });
  await s.waitForSelector(".editor .cm-lintRange-error", { timeout: 10000 });
  const nProblems = await s.$$eval("#problems .item", (x) => x.length);
  check(nProblems > 0, `${scheme}: the problems panel lists the diagnostic`);
  await s.waitForSelector("#output-errors:not([hidden])", { timeout: 10000 });
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
  await s.selectOption("#backend", "lean-model");
  await s.waitForFunction(() => document.querySelector("#output .cm-content")?.textContent.includes("def "), null, { timeout: 10000 });
  await s.mouse.move(5, 5);
  await shot(s, `sandbox-lean-${scheme}`);
  await s.close();
}

await browser.close();
server.httpServer.close();
console.log("\nscreenshots:\n" + shots.join("\n"));
if (problems.length) {
  console.log("\nproblems:\n" + problems.join("\n"));
  process.exitCode = 1;
}
