# lean-girth

Lean formalization of the main draft of *Local forests in structural Ramsey theory* (`janhubicka/girth`).

The project is layered on top of `janhubicka/partite-construction`, which supplies the reusable structural Ramsey, induced partite-construction, and checked sparsening/local-tree infrastructure used by the manuscript.  This repository formalizes the additional girth-specific support geometry and then the main theorem.

Initial formalization target: manuscript `main` as of commit containing `paper/01-introduction.tex` blob `5a5a2f9b7decde23330dd8706e08a7e9606c042f` and `paper/02-ramsey-input.tex` blob `3d3d23c9bcf88a456d65d97d35745353e05f45f7`.

## Circulation revision validation (13 November 2026)

The current proposed girth manuscript is being checked in **numbered tracks 1–8**, separate from the older lettered tracks. See [the track index](docs/validation/numbered-tracks-20261113.md) and [programme issue #1060](https://github.com/janhubicka/lean-girth/issues/1060).

The track index pins the audited 41-page manuscript source digest and identifies already reusable theorems, conditional interfaces, and newly required proofs. **The revised manuscript was not yet merged to its repository's `main` when the index was created.** Existing Lean modules and historical CI gates are intentionally retained; only an exact local build, source-level hypothesis comparison and axiom audit can promote a new statement.
