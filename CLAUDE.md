# Kanon

## Design intentions

- Kanon is meant to be a standalone DSL. It shouldn't hardcode things that Soteria needs in particular, we should instead just extend the DSL to support our use case, while avoiding magic and avoiding adding features whose only purpose is support soteria's use case.
- Kanon is experimental: we don't care about backwards compatibility. It's always ok to remove features, with no nice error messages for transitioning old code; the only Kanon code is ours, and we know what we're doing.
- Kanon is simple. Avoid magic and over-complicated or counter-intuitive features.
- Soteria + Kanon is an experimental setup, where we are attempting to catch unsoundnesses and avoid the current unwieldiness of the whole bv values functor / extensions / solver limitations. Kanon seems a very natural fit for this, because we can tweak it to add features to help us, and its extensibility at the value language level fits perfectly the goals of Soteria. So if something in soteria rust or c got worse because of Kanon, we should take notes on it, and see how Kanon can be improved.

## Changelog

- Every line of `CHANGELOG.md` has at most 10 words and at most two sentences.
- It lists only user-facing changes: syntax, attributes, generated output, CLI, language server, editor support, behaviour, fixes of wrong output. No refactors, tests, CI or design rationale.
- Any further detail (explanations, examples, limits) goes in the reference and the guide (`site/src`).
- Group entries under Added, Changed and Fixed. Breaking changes go under Changed.

## Documentation

- `README.md` is high level only: overview, install, usage and links. All documentation lives in the reference and the guide (`site/src`).
- A new feature is documented in the reference (`site/src/reference`), and in the guide (`site/src/proving`, `site/src/tutorial`) if it needs a how-to, never in the README.

## Git

- Always rebase, never merge: keep a linear history (rebase branches onto their base, integrate other branches by rebasing; force-push with `--force-with-lease` after a rebase).
- Keep each commit subject under 32 characters, all lowercase (unless it references an uppercase keyword, module name, etc.), and keep descriptions minimal and short.
