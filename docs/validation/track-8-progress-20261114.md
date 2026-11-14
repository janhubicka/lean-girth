# Track 8 continuation — leaf charging and induced-trace adapters (2026-11-14)

**Scope:** manuscript labels lem:smalltraces and cor:smallrelational from the merged 41-page structural girth proof; follow-up to merged Lean PR #1062 and manuscript PR #449. This branch has *new source-level Lean proofs* but no local Lean kernel executable; **do not promote validation marks**.

## New Lean declarations

1. Girth/ForestTraceLeafCharging.lean:
   - JoinTree.exists_leaf_private_vertex: in a nontrivial finite join tree with inclusion-incomparable bag carriers, a leaf has a vertex occurring in no other bag (uses JoinTree.exists_leaf_attachment and JoinTree.mem_parent_of_mem_leaf_and_other).
   - JoinTree.exists_injective_representatives: an induction deleting that leaf and its private vertex builds an injection of the bag indices into the vertices, with each chosen representative in its bag. Requires nonempty carriers and antichain; *does not require pairwise allowed support intersections*.
   - JoinTree.card_le_of_antichain: the resulting number-of-bags bound.
   
   This **closes only the counting argument conditional on a join tree of the maximal traces**. It does **not** deduce the join tree of maximal traces from the manuscript's local-completion hypothesis; chordality, local clique coverage and the finite chordal-clique-tree bridge remain to be formalized.

2. Girth/FiniteTraceCoverage.lean:
   - CoversNonemptyTraces is an indexed cover relation allowing only nonempty traces; duplicated carriers are allowed.
   - coversNonemptyTraces_empty selects the empty family on the empty vertex set.
   - CoversNonemptyTraces.vertex_coverage proves every vertex of Z belongs to a selected original member.
   - CoversNonemptyTraces.tuple_coverage proves selected members cover *all positive-arity tuples*, including unary and repeated-coordinate tuples, whenever the original family covers each tuple. It intentionally requires arity > 0. Nullary truth is handled through structural embeddings, not an invented nonempty trace.

3. CheckTrack8LeafCharging.lean imports both and requests #check plus #print axioms on all six lemmas. It is an **unexecuted** kernel gate, not a claim of verification.

## Manuscript alignment

The companion branch revision/track8-leaf-trace-induction-20261114 replaces a rooted-clique-tree charging explanation with deletion of a leaf maximal clique, charging its vertex private from all remaining bags. It also explicitly proves vertex coverage and notes unary and repeated-coordinate tuples in the induced-substructure extraction. The whole proof remains conditional on the genuine outer forest-extension invariant, not just theorem thm:main(iv). The branch changes paper/06-consequences.tex only.

## Adversarial check and numerical diagnostics

- On finite n-point universes with n <= 4, exhaustive independent enumeration finds **no** antichain of nonempty bags with a join tree and without an injective assignment of representative vertices. Counts of join-tree antichains for n=1,2,3,4: 1,4,17,109 respectively. Reproduce independently using `python3 checks/track8_leaf_charging_bounded.py` (it imports the previously merged `checks/track8_small_traces_bounded.py`). This is a **bounded diagnostic**, not a kernel proof.
- The prior exhaustive cover checker was independently rerun: among four-vertex covers, 112 have too many maximal traces; each has a selected three-member subfamily admitting no internal join-tree completion.
- The new Lean proof constructs the injection by leaf induction; it cannot assume the chosen maximal traces themselves have a join tree until the remaining local-to-global bridge is proved.
- The relationship between an A-supported point attachment in Lean and the manuscript's incident-B-constituent support remains an explicit irreducibility adapter.
- No branch should be merged as a theorem-validation mark before a real Lean build and #print axioms check on its exact head.

## Remaining Track 8 route

1. Compile CheckTrack8LeafCharging.lean against the pinned repo toolchain; repair errors, inspect printed axioms.
2. Establish the finite locally-extendible-cover -> chordal pair graph -> conformal traces -> join tree on maximal traces, with the original-cover completion hypothesis and the empty trace case.
3. Feed the resulting selected-copy family into the **actual** outer forest-extension invariant (Track 2 direct join-tree lift, Track 7 recursive witness) and reuse MixedForestInduction.mixedForest_embeds_supportedTree_of_bMemberSupport.
4. Transport positive-arity tuples and vertices using the new exact trace-selection adapters; handle nullary relations by induced embeddings; finish the ordered/unordered copy-colouring extraction.

**Status:** new written Lean proof modules drafted and source-reviewed, build unavailable in this runtime (no lean/lake/elan or downloadable Lean toolchain); no paid GitHub Actions triggered, and no markers changed.

## 14 November evening: sharper modular endpoint

The branch also adds:

- \`Girth/ForestTraceRestriction.lean\`: \`HypergraphPiece.traceCarrier\`, \`JoinTree.traceCarrier\`, and \`setBagPiece_traceCarrier\`. The *same* join tree and its running intersections survive restriction of all bags to Z. This does **not** assert heredity for arbitrary subfamilies.
- \`Girth/FiniteTraceMaximal.lean\`: \`exists_maximal_nonempty_trace\` uses finite partial-order maximality on the actual original-index family; \`maximalTraceRepresentative\` chooses a distinct original member for each distinct maximal nonempty trace; its injectivity is proved, preventing duplicate-index overcounting.
- \`maximalTrace_card_le_of_joinTree\` reuses leaf charging on bags whose **vertices are elements of the subtype Z**, not the ambient universe. \`maximalTrace_selection_ncard_of_joinTree\` proves the numerical bound on the actual SELECTED ORIGINAL MEMBERS using \`Set.ncard_range_of_injective\`. \`smallTrace_selection_of_maximalJoinTree\` handles **both** the nonempty and empty trace cases, giving exactly a selected family with \`selected.ncard ≤ Z.ncard\`.

The sole combinatorial **hypothesis** of \`smallTrace_selection_of_maximalJoinTree\` is \`hTree\`: any nonempty family of distinct maximal original traces must have a join tree. It still needs to be **proved from** the manuscript's bounded internal completion assumption, via chordality/conformality (and a chordal clique-tree theorem). Do not treat the conditional endpoint as validation of lemma lem:smalltraces. Mathlib's current graph library does not supply the whole chordal clique-tree bridge as a ready-to-use verified theorem for this project.

The exact-head check file was updated with checks and axiom-print requests for the new declarations. No Lean binary was installed or invoked; no new validation marks were promoted.


## Further 14 November work: original-index maximalization and pair graph

- \`Girth/FiniteTraceMaximal.lean\` now produces exactly the conclusion needed from the combinatorial lemma: \`smallTrace_selection_of_maximalJoinTree\` constructs \`selected : Set ι\`, proves \`CoversNonemptyTraces F Z selected\`, and proves **\`selected.ncard ≤ Z.ncard\`**. Duplicate original indices are controlled by the injective representative choice. The empty family of nonempty traces is treated separately, without inventing any nonempty trace or demanding a cover member for an empty Z. Its single explicit extra input \`hTree\` is **not** proved by the file.
- \`Girth/FiniteTracePairGraph.lean\` isolates \`tracePairGraph\` and \`TraceConformal\`: it proves every original trace is a graph clique, a maximal original trace is a maximal clique under conformality, and conversely every maximal nonempty clique equals a maximal original trace. This is the precise graph-to-bags adapter required after the chordality/conformality argument, not a chordal graph theorem.
- \`Girth/ForestTraceRestriction.lean\` provides the restriction of all original completion bags to Z, preserving exactly their running intersections and their original index type.

**Remaining independent mathematics, in recommended formal order:**

1. Prove subtree Helly for finite \`SimpleGraph.IsTree\` and the induced-occurrence-subtree interface from \`Girth/Forest.lean\`.
2. Use Helly to show that every clique with no original containing trace produces ≤|Z| chosen cover members with no internal join-tree completion (minimal uncovered clique).
3. Show that an induced chordless cycle in the trace pair graph produces ≤|Z| *distinct* original edge-supporting members, and its restricted join-tree completion is impossible (chordality).
4. Construct a clique join tree of the finite chordal pair graph and transfer it, by conformality, to \`maximalTracePiece\`; discharge \`hTree\`.
5. Only then close the general small-trace lemma and use exact outer actual-copy forest completion for the induced relational corollary.

**No status inflation:** these are manually drafted Lean proofs; exact-head elaboration and \`#print axioms\` have not run. A static no-holes/delimiter scan is not a kernel certificate. The external EHN Ramsey input and the Tracks 2/7 recursive outputs remain separate from these finite combinatorial lemmas.
