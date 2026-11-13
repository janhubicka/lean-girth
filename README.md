# lean-girth

Lean formalization of the main draft of *Local forests in structural Ramsey theory* (`janhubicka/girth`).

The project is layered on top of `janhubicka/partite-construction`, which supplies the reusable structural Ramsey, induced partite-construction, and checked sparsening/local-tree infrastructure used by the manuscript.  This repository formalizes the additional girth-specific support geometry and then the main theorem.

Initial formalization target: manuscript `main` as of commit containing `paper/01-introduction.tex` blob `5a5a2f9b7decde23330dd8706e08a7e9606c042f` and `paper/02-ramsey-input.tex` blob `3d3d23c9bcf88a456d65d97d35745353e05f45f7`.

## Circulation revision validation (13 November 2026)

The current proposed girth manuscript is being checked in **numbered tracks 1–8**, separate from the older lettered tracks. See [the track index](docs/validation/numbered-tracks-20261113.md) and [programme issue #1060](https://github.com/janhubicka/lean-girth/issues/1060).

The 41-page audited manuscript is **merged to [`janhubicka/girth/main@8c9cfa6e`](https://github.com/janhubicka/girth/commit/8c9cfa6eb6d817a08f3009fe048fc0be07426ece)**. The pre-merge annotated tag preserves the original `main@c195cdba`. The [numbered index](docs/validation/numbered-tracks-20261113.md) fixes the exact source digest and distinguishes reusable checked theorems from conditional interfaces and new obligations. **No new Lean proof certification is implied by the manuscript merge.** Existing checked modules and historical gates remain intact; promote only after an exact source/hypothesis comparison, local build and `#print axioms` audit. This repository's `lean.yml` triggers a full build on every branch push, so create numbered validation branches when actual proof changes are ready, not eight empty branches at once.
