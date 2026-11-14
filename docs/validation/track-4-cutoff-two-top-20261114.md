# Numbered Track 4: deriving the cutoff-two local witness at universal top

**Status:** mathematical argument checked at the source level; new Lean declarations in draft PR #1064 are **not compiled**. No changes to the frozen circulation manuscript or validation marks should be promoted on this basis.

## Why bottom mixed forests through 2 do not imply bottom system girth >2

Let A be an ordinary graph edge. Take a six-vertex graph with vertices
`u1,u2,v1,v2,x,y` and the six edges
`f=u1u2`, `e=v1v2`, `ax=u2x`, `bx=v1x`, `cy=v2y`, `dy=u1y`.
These form one ordinary graph six-cycle; their physical support is linear.

Use four designated induced 2-edge paths:
- `F_A`: edges `f,ax`, vertex carrier `{u1,u2,x}`;
- `F_B`: edges `e,bx`, vertex carrier `{v1,v2,x}`;
- `F_C`: edges `e,cy`, vertex carrier `{v1,v2,y}`;
- `F_D`: edges `f,dy`, vertex carrier `{u1,u2,y}`.

Every pair among these four complete support pieces **and all six ambient one-edge support pieces** has an allowed intersection: the four adjacent designated pairs intersect successively in `{x}`, the complete edge `e`, `{y}`, the complete edge `f`; the opposite pairs are disjoint. Pairwise designated-vs-one-edge intersections are empty, single vertices, or the one edge that the designated path itself owns. Pairwise distinct ambient graph edges meet in at most one vertex. Consequently the finite-SET mixed forest condition through cutoff 2 holds (all 45 distinct pairs checked exhaustively in a local enumeration).

Nevertheless, at the **bottom equality wagon cut**, the original selected-labelled big cycle
`F_A, x, F_B, wagon(e), F_C, y, F_D, wagon(f)`
has length four and twice-order four, hence order two. It satisfies A1--A3: all its occurrences are mixed, the two wagon connectors have no incident vertex connectors, and each other wagon sees at most one vertex connector. It has no global supreme original designated copy, since none of the four paths owns both `e` and `f`. Thus bottom FullSystemGirthGT 2 does NOT follow from the mixed forest condition through 2 alone. This example is a counterexample to that *shortcut*, not to the one-step picture-preservation theorem.

## Why the universal TOP does have full system girth >2

Assume a physical order-one pretrain satisfies:
1. LinearPretrain (physical edge linearity plus the wagon-intersection bound);
2. every physical edge has the same wagon parent;
3. every vertex in a designated copy is covered by one of its own physical A-edges;
4. every ambient A-edge meeting a designated copy in at least two vertices belongs to that designated copy (the actual A-strongness condition).

Then every acceptable big cycle of order at most two has an ORIGINAL designated supreme plan.

- Source length 2: physical linearity and A1 force a designated label. For mixed vertex/wagon connectors, an owned edge through the vertex also lies in the universal wagon. For two vertex connectors x,y, either an ambient edge joins x,y (A-strongness makes it owned, giving a short replacement), or none does (choose distinct owned edges through x and y, giving a legal long piece in the common wagon). Distinct wagon/wagon connectors are impossible. The existing strict two-cycle local-to-global constructors provide a fully legal global replacement word.
- Source length 3: since all wagon connectors have the same label, there is at most one wagon connector. The order budget rules out an all-vertex word, so the pattern is vertex/wagon/vertex, up to rotation. A2 prohibits any A-edge joining the two vertex connectors because both lie in the universal wagon. Thus the occurrence between them is designated, and its two owned incident edges give short replacements for both other occurrences. The existing simultaneous all-short constructor produces a genuine global plan.
- Source length 4: all four twice-weights would have to be one, so the connector kinds must alternate. This requires two distinct wagon connector positions, impossible for one universal wagon. The basic length-vs-twice-order inequality excludes all longer sources.

## Actual finite-set F_(2) application

For the genuine active-gluing witness on a local core R:
- The finite mixed forest condition through 2 implies ordinary A-support girth >2, hence A-linearity in R (every ambient A-edge is tested).
- The same pairwise mixed forest condition implies A-strongness of each selected gluing copy (it is tested against every ambient A-edge).
- Every vertex of the active source lies in an A-copy, and each selected embedding transports the complete A-support; this gives the required owned-edge vertex coverage.
- At the universal top, the exact train relation identifies every pair of physical A-edges, so their quotient wagon labels have one common parent.

Therefore the local witness at `μ=top` has `FullSystemGirthGT 2`. This is exactly the existential input required in the existing `ActiveAttachmentBounds.cutoffTwo` field when the leading cutoff equals 2. It does **not** assert a top coordinate in the output vector or wrongly infer bottom local system girth.

## New source-only Lean declaration map

- `TrainUniversalTopTwoCycleSupreme.lean`: actual original n=2 owned short/long global plan, physical one-wagon exclusion;
- `TrainUniversalTopThreeCycleSupreme.lean`: designated n=3 central occurrence and simultaneous short plan;
- `TrainUniversalTopOrderTwoClassification.lean`: no four-position order-two word at universal top, n=3 connector classification, and full abstract `OrderOneData.fullSystemGirth_two_of_constant_parent`;
- `TrainActualWitnessTopTwoFromMixed.lean`: actual source A-support/strongness and local FullSystemGirthGT 2 at top from the finite mixed forest through 2;
- `TrainActualCutoffTwoFromMixed.lean`: the exact `ActiveAttachmentBounds.cutoffTwo` proposition.

**Validation gates:** Exact-head `lake env lean CheckTrack4MinimumOwnerSwap.lean`, inspect `#print axioms`, and independently audit edge incidence, the A2 central nonedge clause, and output-plan legality. The source path may contain elaboration errors and must not be merged as verified before these checks.
