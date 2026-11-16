# Track 1 — combined selected coloured Ramsey witness and actual mixed LF2

**16 November 2026. Status:** mathematics/API candidate on a stacked
development branch; **NOT** compiled or kernel-certified at this exact
head. The verified foundations are merged PRs
[#1069](https://github.com/janhubicka/lean-girth/pull/1069),
[#1074](https://github.com/janhubicka/lean-girth/pull/1074), and
[#1079](https://github.com/janhubicka/lean-girth/pull/1079).
The upstream unverified selected-EHN physical normalization is draft
[#1078](https://github.com/janhubicka/lean-girth/pull/1078).

## The new actual local-witness interface

`Track1ColouredSelectedWitnessAssembly.lean` combines, **in a single
output with one common order and one physical selected family**:

1. A genuine full induced coloured ordered embedding of every
   selected B copy into the **induced restriction to used vertices**,
   by `Track1FullSelectedWitnessEmbeddings`;
2. coverage of *every* positive split edge by that same family,
   by `Track1ActualSelectedCoverage`. No assumption that the
   original EHN witness was covered by selected targets;
3. support girth greater than a parameter `g ≥ 2`, by inheriting
   the original EHN girth through the selected-support subhypergraph
   and `Track1OwnerSplitGirth`. This serves both g=2 and g=3;
4. pairwise permitted selected B-support intersections, using the
   **exact common physical A-edge in both source supports**, by
   `Track1ActualSelectedLiftPairwiseAllowed`;
5. strong inducedness of each selected lifted B image with respect
   to positive A-edges, **derived** from the actual old A-strong
   image and support-edge membership, by
   `Track1ActualSelectedBStrong`;
6. **actual mixed LF2 through two** for all selected lifted B supports
   together with **every** ambient split positive one-edge member,
   via the direct two-member join-tree lemma described below;
7. the selected edge-colouring arrow, via the checked old-support
   colour transfer and the actual selected EHN arrow.

Every output property is derived from the displayed genuine
old selected EHN family hypotheses. In particular the source
forbidden-vertex degree-one condition is a consequence of the
source's allowed-predicate intersection restriction.

## Direct mixed LF2 instead of extra unsplit transport

`Track1SplitSelectedMixedLF2.lean` promotes the elementary fact
that **any pairwise allowed family of at most two members is a
forest**. The proof is the same star-tree argument as the checked
private two-member proof in `TrainRecursiveBaseRamsey`, but
polymorphic across the index and split-vertex universes.

The full mixed family is indexed by the disjoint sum of:
- actual selected B-support pieces; and
- every ambient positive split edge as a one-edge member.

Its pairwise cases are elementary:
- B–B: the already derived selected-family controlled overlap;
- B–edge: if two distinct vertices are common, selected B
  strongness forces the entire physical edge into the B support,
  otherwise the intersection is a singleton;
- edge–edge: `GirthGT splitPhysicalEdges 2` gives linearity.

Thus **no new local-forest assumption on the split witness** is
required at cutoff three. The subsequent actual true-active
attachment still needs to carry these source pieces to its core
and identify them with its actual `mixedOwnerSmall` family.

## Upstream proof inputs and remaining gaps

The physically indexed triangle-free EHN selected family in
`Track1TriangleFreePhysicalFamily` is intended to provide the
strong image, controlled intersection, injective physical support,
common fresh EHN order, support girth and selected Ramsey arrow.
The coloured predicate on its selected B images is read from
the witness's genuine unary relations. The whole coloured
one-edge presentation is obtained from the checked
`colouredOrderedEdgeSupport_exact` and the staged
`Track1EHNColouredPresentation` adapter.

The actual (m=3) forest picture increment
`actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull`
is **already checked only as a conditional theorem**. Still
missing are its genuine partite maps/active source factorization,
the identification of the new mixed LF2 support family with the
attached core's small gluing owners, core/ambient girth and
the backward Ramsey fusion through the ordered base edges.
Restoring ORIGINAL target-isolated vertices in their given parts
and order remains the final output step.

## Verification

`CheckTrack1ColouredSelectedWitness.lean`: ten explicit
`#print axioms` probes.
`scripts/check_track1_coloured_selected_witness.sh`:
focused dependency build, rejection of explicit proof placeholders,
and strict `scripts/check_axioms.py` inspection.

These checks have **not yet run** on the new declarations.
Neither `lem:unrestricted` nor `prop:forestthree` should
be marked fully Lean-verified until the required actual interfaces
and end-to-end proof have compiled successfully.
