export function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => `&#${c.charCodeAt(0)};`);
}

/** `f`, called `ms` after the last of a series of calls. */
export function debounce<A extends unknown[]>(f: (...args: A) => void, ms: number) {
  let timer: ReturnType<typeof setTimeout> | undefined;
  const d = (...args: A) => {
    clearTimeout(timer);
    timer = setTimeout(() => f(...args), ms);
  };
  d.cancel = () => clearTimeout(timer);
  return d;
}
