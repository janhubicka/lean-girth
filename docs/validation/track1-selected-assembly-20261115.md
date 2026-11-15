# Track 1 — next selected-witness integration (15 November 2026)

**Staging only:** [branch validation/1-ordered-copy-packaging-20261115](https://github.com/janhubicka/lean-girth/tree/validation/1-ordered-copy-packaging-20261115), based on PR #1069's current repaired candidate `f24cb19d`. It is deliberately **separate** from the compiling [PR #1069](https://github.com/janhubicka/lean-girth/pull/1069), so the exact-head CI run there is not cancelled. Nothing here is a kernel certificate until an exact-head check succeeds.

## New conditional Lean proof pieces

| Module | Statement and prior checked theorem |
| --- | --- |
| `Track1SelectedSupportColourArrow` | Define `selectedSupportEdges A family` as the actual union of positive selected A-carriers. An embedding colouring of all A copies induces an edge colouring on this selected union; reverse by extending arbitrary edge colours to all A embeddings. |
| `Track1SelectedActualOwnerCopies` | Define the old owner-split hypergraph with exactly those selected edges, and construct one canonical `ColouredOwnerSelectedCopy` per actual selected B embedding, using `ColouredOwnerSelectedCopy.ofEdgeEmbedding`. The marked-degree-one hypothesis is explicitly required. |
| `Track1ActualSelectedOwnerColourArrow` | Compose the selected EHN embedding arrow with the physical-edge constructor. Deduce the EXACT old edge-colouring arrow required by the checked `ColouredEdgeOwnerSplit.selectedColourTransfer`. |
| `Track1FullSelectedOrderedLifts` | Use the checked `exists_projectionFirstLinearOrder` and `ownerSplit_lifted_colouredOrderedEmbedding` to get **one common linear order and complete induced coloured ordered embeddings** of every selected target, including global `(x,⊥)` tags for isolated marked vertices. |
| `Track1FullSelectedSupportPieces` | Construct the actual lifted B-support pieces and derive their allowed pairwise intersections from the checked `lifted_pair_intersection_subsingleton` and `lifted_intersection_eq_splitEdge`, including correct membership of a shared whole edge in both pieces. |
| `Track1OwnerSplitFinite` | Deduce finiteness of the owner-token vertices from finite old EHN vertex type, without adding an independent finiteness premise. |
| `Track1OrderedPhysicalOwners` | In the globally ordered source case, distinct indexed embeddings have distinct full physical B-support pieces; reuse the existing `ordered_embedding_eq_of_sameCopy` rather than choosing duplicate-support representatives. |

There is a dedicated `CheckTrack1SelectedAssembly.lean` file (10 strict axiom probes) and `scripts/check_track1_selected_assembly.sh` (focused Lake compilation followed by the repository's existing `scripts/check_axioms.py`).

## Remaining exact interfaces — not assumed proved

1. **Old coloured relational presentation.** From the actual expanded selected EHN family (`Track1TriangleFreeSelectedFamily`) and its fresh global order, produce the full induced old embeddings in `colouredOrderedEdgeTarget k ...` used by `ownerSplit_lifted_colouredOrderedEmbedding`. This is a translation from the original edge-type relation, unary predicates, and within-predicate orders; it must not be hidden by asserting that the output is induced.
2. **Support-edge reflection.** The checked `Track1SelectedOldStrong` bridge supplies the owner-split `hOldStrong` hypothesis from an actual A-strong selected B image, provided each retained old edge is literally an A-copy and the selected source edges are all `supportCopies A B`.
3. **Selected intersections.** Convert the old EHN “empty, singleton, common A-copy” condition into the actual common physical source edge requirement in both selected copies. An old whole intersection does not suffice unless it is an edge of both source B-supports. `Track1FullSelectedSupportPieces` makes this exact membership premise explicit.
4. **Finite carrier and restricted output.** The H.Vertex owner-token type has many unused tags. Its `Finite` instance follows from the finiteness of original vertices; the final witness is induced on `selectedLiftCarrier`, not the untrimmed owner-token type. Already staged `Track1OwnerSplitCoverage` ensures all output edges are supported there.
5. **Partite fusion.** The checked `Track1SelectedMixedLF2` gives the *actual mixed two-member forest* including all ambient A-edges. Together with triangle-free core girth and old mixed LF3, specialize `actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull` at `m=3`. The true-active maps, selected part-preserving family, backwards Ramsey fusion, order coarsening and private restoration of the ORIGINAL isolated target vertices remain separate obligations.

## Safe check command

```bash
git switch validation/1-ordered-copy-packaging-20261115
bash scripts/check_track1_selected_assembly.sh
```

This source has **not** been compiled or axiom-checked. The known-good results remain the previously checked generic owner-splitting and mixed-forest components. A green staged check would certify only its seven conditional theorem closures, NOT `lem:unrestricted`, `lem:threepicture` or `prop:forestthree` end-to-end.
