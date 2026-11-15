# Track 1 — physically normalized selected EHN family (15 November 2026)

Status: **mathematical audit and uncompiled Lean candidate**.
This note concerns the continuation branch
`validation/1-actual-partite-interface-20261115`, not the already
kernel-checked Track 1 foundation on `main`.

## Remove a dead end: embedding labels are not physical copies

An arbitrary set of selected embeddings of a target B can contain two
different embeddings with the same image carrier. The old draft
`Track1OrderedPhysicalOwners` relied on an order-uniqueness lemma that
was not identified in the checked API and tied the geometry to ordered B.

Use **physical carriers** instead:

* `Track1PhysicalBCarrier family` consists of subsets S in the old
  ambient witness which are genuine images of *some* EHN-selected
  full B embedding.
* `track1_physicalRepresentative family` chooses an embedding
  **from the original selected family** for each such S.
* Distinct indices now have distinct B image carriers, hence distinct
  complete B-support pieces (including the same isolated vertices).
* Strongness and controlled intersections transfer verbatim to the
  representatives, because each is a genuine selected embedding.

### Why the Ramsey arrow survives representative choice

Suppose the EHN arrow selects an embedding b with all its A-subcopies
monochromatic. Let b' be the chosen representative for the same
physical image carrier S. For **every** A-embedding a into B, the
composite b'∘a is an A-copy inside S. As b is a full induced embedding
onto S, this composite factors through b as b∘a' for a genuine
A-embedding a' into B. Thus its colour is the same as the colour of
all A-subcopies of b. The representative b' is monochromatic as well.

No rigidity, finite-order uniqueness or new Ramsey theorem is needed.
The proof uses only factorization into the induced B image.

## New proof chain (uncompiled)

1. `Track1PhysicalSelectedRepresentatives.lean` proves physical
   injectivity **and** the Ramsey-arrow preservation just described.
2. `Track1TriangleFreePhysicalFamily.lean` combines that normalization
   with the already checked
   `track1_selectedOrderedRamseyFamily_triangleFree`. It returns a
   single indexed family with physical B-support injectivity, common
   auxiliary order, A-strongness, controlled intersections and the
   actual EHN selected arrow.
3. `Track1PhysicalFamilyActualMixedLF2.lean` feeds those same
   representative B copies into the **checked**
   `track1_actualMixedLF2_of_strong_controlled`. Ambient A-edges are
   preserved; no selected-edge pruning is assumed during attachment.
4. `Track1PhysicalActualSelectedIntersections.lean` uses the same
   representative family for owner splitting and passes the existing
   small/whole-common-edge intersection theorem.
5. The separate `Track1ControlledPhysicalIntersection.lean` derives
   membership of the exact common physical A-edge in **both**
   original selected B supports; source forbidden-degree-one follows
   from the original allowed-predicate intersection restriction.
6. Existing `Track1EHNColouredPresentation.lean` and
   `Track1FullSelectedWitnessEmbeddings.lean` identify the source
   k-edge relation and construct the induced ordered lifted selected B
   images on the union of their actual carriers.

The redundant modules `Track1OrderedPhysicalOwners`,
`Track1EHNIndexedSelected`, `Track1OrderedFamilyActualMixedLF2`
and `Track1OrderedActualSelectedIntersections` are removed in this
branch. The new normalized versions **replace** them, rather than
coexisting as unused proof attempts.

## Exact validation boundary

`CheckTrack1ActualPartite.lean` currently contains **15** axiom probes.
`scripts/check_track1_actual_partite.sh` builds the appropriate
dependency roots and invokes the strict existing axiom checker.
A static import/placeholder inventory has passed, but **no Lean
elaboration or axiom output has been obtained for this branch**.

Upstream [PR #1074](https://github.com/janhubicka/lean-girth/pull/1074)
has its own first-layer assembly gate; its exact-head job was still
queued on last check. Avoid merging these continuation candidates
until the upstream compiler errors are resolved and this branch's own
focused gate passes.

## What still separates this from the full m=3 theorem

The selected local Ramsey arrow and mixed LF2 must be inserted into
the *actual* partite attachment at each active base edge. The checked
conditional theorem
`actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull`
requires the genuine source/factorization, true-active carrier,
nonpruned ambient support, base A-strongness and core/ambient girth
hypotheses. Then backward finite-colouring fusion must be proved
and original target isolated vertices restored compatibly with the
final linear order.

None of these remaining steps is removed by physical normalization,
and no new manuscript validation mark is justified by this draft.
