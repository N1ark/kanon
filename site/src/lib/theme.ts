// Light or dark: the system's until the header's toggle picks one, remembered under one key by
// both pages.
import { applyTheme, bootTheme, liveTheme, storedThemeMode } from "purr";

const KEY = "kanon-theme";

/** Before mounting, so the first frame is in the remembered theme. */
export function startTheme() {
  bootTheme(KEY);
  applyTheme({ mode: storedThemeMode(KEY), storageKey: KEY });
}

export function toggleTheme() {
  applyTheme({ mode: liveTheme.dark ? "light" : "dark", storageKey: KEY });
}
