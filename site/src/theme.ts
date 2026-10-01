// The theme: the system's (prefers-color-scheme), or light or dark, chosen
// with the button of the header and remembered. index.html and sandbox.html
// set data-theme before the page renders, from the same storage key.

import { storage } from "./util";

type Theme = "auto" | "light" | "dark";
const KEY = "kanon-theme";
const labels: Record<Theme, string> = { auto: "Theme: system", light: "Theme: light", dark: "Theme: dark" };
const icons: Record<Theme, string> = { auto: "◐", light: "☀", dark: "☾" };

const listeners: (() => void)[] = [];

/** Called when the theme changes. */
export function onThemeChange(f: () => void) {
  listeners.push(f);
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", f);
}

function apply(t: Theme) {
  if (t === "auto") delete document.documentElement.dataset.theme;
  else document.documentElement.dataset.theme = t;
  const b = document.querySelector<HTMLButtonElement>(".theme-toggle");
  if (b) {
    b.textContent = icons[t];
    b.title = labels[t];
    b.setAttribute("aria-label", labels[t]);
  }
  listeners.forEach((f) => f());
}

export function initTheme() {
  let t = (storage.get(KEY) as Theme | null) ?? "auto";
  if (!(t in labels)) t = "auto";
  apply(t);
  document.querySelector(".theme-toggle")?.addEventListener("click", () => {
    const order: Theme[] = ["auto", "light", "dark"];
    t = order[(order.indexOf(t) + 1) % order.length];
    storage.set(KEY, t);
    apply(t);
  });
}
