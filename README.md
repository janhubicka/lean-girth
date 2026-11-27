# lean-girth

## Current proof: local validation on 27 November 2026

The contact-graph proof of `regular-tree-girth.tex` now builds locally with
Lean **4.35.0-rc3**. The complete main relational theorem, its literal
carrier-set formulation, the unordered hypergraph theorem, the order-extension
corollary, both small-size induced-substructure consequences, and the full
chordality characterization for arbitrary induced vertex sets have passed
strict transitive axiom audits. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. The proof does not assume the girth Ramsey theorem.

Run the complete focused build and audit with:

```sh
bash scripts/check_contact_validation.sh
```

`Girth.lean` imports the final aggregate
[`Girth/ContactValidation.lean`](Girth/ContactValidation.lean), so the default
build includes the final application theorems. The aggregate also retains the
previous regression imports. Historical proof files remain available without
being part of this active build.

| Manuscript statement | Main Lean declaration |
| --- | --- |
| Recursive train Ramsey theorem | `contactProfileRamsey_wellFounded` |
| Local-forest partite lemma | `contactLocalForestPartite` |
| Relational local-tree girth Ramsey theorem, literal copy families | `contactRelationalGirthRamsey_carriers` |
| Unordered girth and local-forest Ramsey theorem | `contactUniformLocalRamsey` |
| Order-extension corollary | `contactCompleteOrder_fullCorollary` |
| Induced relational substructures with at most n vertices | `contact_small_induced_supported` |
| Induced supported-tree embedding iff the comparison graph is chordal | `contact_induced_supported_iff_chordal` |
| Small induced subhypergraphs, including edgeless targets | `contactUniformSmallRamsey` |
| Arbitrary metric triangulation and shared-chord criterion | `contactSharedChordBound_iff_metricG4` |
| Join trees iff admissible enumerations | `contact_joinTree_iff_admissibleRank` |
| Exact one-added-copy completion sharpness | `contactSharp_actual_completion` |
| Exact vertex-cutoff sharpness with all five witness clauses | `contact_vertex_cutoff_sharp` |

See the [local validation record](docs/validation/contact-final-20261127.md)
for the exact statement scope, dependency pins, sharpness certificates, and
reproducible build and axiom-audit results. The manuscript's newly promoted
validation links have a separate declaration audit in
[`CheckContactManuscript.lean`](CheckContactManuscript.lean).

## Earlier validation history

Lean formalization of the main draft of *Local forests in structural Ramsey theory* (`janhubicka/girth`).

The project is layered on top of `janhubicka/partite-construction`, which supplies the reusable structural Ramsey, induced partite-construction, and checked sparsening/local-tree infrastructure used by the manuscript.  This repository formalizes the additional girth-specific support geometry and then the main theorem.

Initial formalization target: manuscript `main` as of commit containing `paper/01-introduction.tex` blob `5a5a2f9b7decde23330dd8706e08a7e9606c042f` and `paper/02-ramsey-input.tex` blob `3d3d23c9bcf88a456d65d97d35745353e05f45f7`.

### Circulation revision validation (13 November 2026)

The current proposed girth manuscript is being checked in **numbered tracks 1–8**, separate from the older lettered tracks. See [the track index](docs/validation/numbered-tracks-20261113.md) and [programme issue #1060](https://github.com/janhubicka/lean-girth/issues/1060).

The 41-page audited manuscript is **merged to [`janhubicka/girth/main@8c9cfa6e`](https://github.com/janhubicka/girth/commit/8c9cfa6eb6d817a08f3009fe048fc0be07426ece)**. The pre-merge annotated tag preserves the original `main@c195cdba`. The [numbered index](docs/validation/numbered-tracks-20261113.md) fixes the exact source digest and distinguishes reusable checked theorems from conditional interfaces and new obligations. **No new Lean proof certification is implied by the manuscript merge.** Existing checked modules and historical gates remain intact; promote only after an exact source/hypothesis comparison, local build and `#print axioms` audit. This repository's `lean.yml` triggers a full build on every branch push, so create numbered validation branches when actual proof changes are ready, not eight empty branches at once.
