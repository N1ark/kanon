// Debugging aid: opens a page of dist/ in headless Chromium and prints the
// result of a JavaScript expression.   node scripts/debug-page.mjs PAGE EXPR
import { chromium } from "playwright-core";
import { preview } from "vite";

const [pagePath = "", expr = "document.title"] = process.argv.slice(2);
const server = await preview({ preview: { port: 4180 }, logLevel: "warn" });
const browser = await chromium.launch({ executablePath: process.env.CHROMIUM });
const page = await browser.newPage();
page.on("console", (m) => console.log(`console.${m.type()}: ${m.text()}`));
page.on("pageerror", (e) => console.log(`page error: ${e.message}`));
await page.goto(server.resolvedUrls.local[0] + pagePath);
await page.waitForTimeout(3000);
console.log(await page.evaluate(expr));
await browser.close();
server.httpServer.close();
