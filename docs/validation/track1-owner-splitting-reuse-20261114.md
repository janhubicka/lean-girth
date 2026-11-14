# Track 1 — alternate coloured Ramsey extraction using checked owner splitting

**14 November 2026. Status: candidate integration, not kernel-validated.**

- Main manuscript: `girth/main` (moving, original audited 41-page baseline `8c9cfa6e`).
- Existing preferred functional-closure draft: [girth PR #452](https://github.com/janhubicka/girth/pull/452), unmerged.
- New *comparison only* manuscript branch:
  [`revision/track1-owner-split-reuse-20261114`](https://github.com/janhubicka/girth/tree/revision/track1-owner-split-reuse-20261114).
- Canonical validation issue: [#1052](https://github.com/janhubicka/lean-girth/issues/1052).

## Why this may be the faster route

Both English proofs begin with the **unmarked canonical pair/ternary
functional EHN witness**. The first route adds an arbitrary unary
function `d` to the EHN language to prevent forbidden intersections
*among selected target edges*. The alternate route uses **no extra
function symbol**: keep only selected target edges, then separate the
forbidden-predicate vertex incidences by old physical edge and make
the isolated forbidden vertices private to each selected target.
Only this initial auxiliary witness changes; the recursive
partite/train representation stays intact.

Existing checked Lean infrastructure nearly covers this operation:

| Existing declaration/module | Required role |
| --- | --- |
| `Girth/TrainColouredEdgeOwnerSplit` | `splitEdge_injective`, `projection_splitEdge`, `intersection_only_allowed` |
| `Girth/TrainColouredOwnerSelectedLift` | `ColouredOwnerSelectedCopy.lift`, `lift_source_edge`, private forbidden isolated vertices |
| `Girth/TrainColouredOwnerSelectedStrong` | `selected_strong_of_old`, no new old contacts |
| `Girth/TrainColouredOwnerWholeEdgeIntersection` | `lifted_intersection_eq_splitEdge` |
| `Girth/TrainColouredOwnerInducedUniformLift` | induced uniform-edge and full ordered coloured lift |
| `Girth/TrainColouredOwnerProjectionOrder` | `exists_projectionFirstLinearOrder`, `selectedLift_strictMono_of_projectionFirst` |
| `Girth/TrainColouredOwnerExactColourTransfer` | `physicalSplitEdgeEquiv`, `selectedColourTransfer`, `selectedSplitPhysicalEdges_exact` |

## New draft theorem candidates on this branch

- `Track1TriangleFreeSelectedFamily`: **fresh-order-respecting selected B family** directly in the triangle-free canonical closure class; it reuses `targetClosureLift` and closed-image geometry without a duplicate unmarked intermediate module.
- `Track1OwnerSplitGirth`: for every `g`, `GirthGT H.edges g` implies `GirthGT H.splitPhysicalEdges g`. Each connector between distinct split edges is an allowed unsplit vertex, so the cycle projects injectively on connectors and physical edges.
- `Track1OwnerSplitCoverage`: define output carrier as `selectedLiftCarrier` (union of selected lift ranges), output edges as `selectedLiftEdges`. Prove every selected edge is contained in that carrier. Under the explicit old-edge selected-cover hypothesis, all physical split edges are retained.
- `Track1OwnerSplitOrderArrow`: one global projection-first order on the token vertices, together with the colour-arrow transfer for the selected old family.
- `Track1CutoffThreeReuse`: direct 3-boundary forest adapter to checked `selectedForest_of_distinctOwners_girthOnly`. The bespoke uncompiled Fin-3 Lean proof was removed; the paper retains its elementary English argument.

Every one of these new files is an **UNCOMPILED DRAFT**, even though it
contains no intentional `sorry` and displays `#print axioms`. No green
manuscript status follows without an exact-head build and axiom report.

## Exact remaining end-to-end obligations

1. Prove the `A`-girth>3 subclass of the canonical `c_A,c_B`
   free-amalgamation class, with no additional function.
2. Compile and audit `track1_selectedOrderedRamseyFamily_of_monotone_embeddings`
   (the previous public EHN endpoint returned only an unindexed arrow).
3. Package the old selected B embeddings as actual
   `ColouredOwnerSelectedCopy` objects with exact physical old edge
   carriers and the source forbidden-degree-one hypothesis.
4. Use `ownerSplit_lifted_colouredOrderedEmbedding` and the
   selected carrier restriction to return actual strong induced,
   order-preserving coloured-edge copies of B; prove physical
   selected-family intersections and the whole Ramsey arrow
   on this restricted structure.
5. Apply the existing `actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull`
   at `m=3` under the true active boundary adapters; then run
   backward fusion and restore isolated target vertices as required.

The owner split is **not** a replacement for the finite triangle-free
EHN theorem nor for the actual picture-step strongness/overlap
adapters. It only eliminates the new arbitrary-unary EHN language
and uses the earlier checked extraction machinery.

## Finite evidence, independently executed locally

A finite script exhaustively enumerated 285,200 admissible one/two
selected-copy families, plus 24,349 seeded three-copy families,
on 166 five-vertex graph supports and 26 five-vertex 3-uniform
supports (each linear and triangle-free). All 309,549 passed,
including 131,640 (graph) and 1,360 (3-uniform) cases with a
marked vertex isolated inside a selected source, and the shared
physical-edge cases. The script also checks exact selected edges,
strongness, pair intersections and 3-cycle exclusion in each split
output. These are bounded diagnostics, **not** Lean proofs or a
Ramsey theorem check.

## Branch policy

Keep the arbitrary-unary route and the owner-splitting route
separate for comparison. Neither is merged. Avoid new GitHub
Actions solely to change the draft, and do not promote proof
markers until the exact current sources and `#print axioms`
are checked.
