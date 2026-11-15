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

## Leaf-induction Helly reduction (new)

\`Girth/ForestJoinTreeHelly.lean\` now gives a direct **recursive Lean proof source** for \`JoinTree.pairCovered_in_one_bag\`. For nonempty K, assume every two (including equal) vertices occur together in some original bag of a finite join tree. Choose a leaf. If it already contains K, finish. Otherwise pick x0 in K outside the leaf; any pair formerly witnessed only in that leaf occurs together in the parent, because its two vertices also appear with x0 in bags outside the leaf. Delete the leaf, preserve pair coverage, and recurse. This avoids importing a separate general finite-subtree Helly theorem.

\`Girth/FiniteTracePairGraph.lean\` applies the new Helly declaration to prove \`traceConformal_of_joinTree\`: a running-intersection family of all original bags, restricted to Z and covering Z, has a conformal pair graph. Diagonal pairs use explicit vertex coverage; distinct pairs use the pair-graph edge witnesses. The reverse direction (no induced cycle in the pair graph of a tree of bags) and local-to-global clique-tree construction remain unformalized.

**Manual source audit only.** The new Helly proof is recursive on the number of join-tree labels; its \`termination_by\` decreases by removing the leaf. As for all new Track 8 code, its source has not yet been accepted by the Lean kernel or checked with executed \`#print axioms\`.


## 14 November late: local-completion-to-conformality source proof

An additional adversarial source audit found an **actual Mathlib API error** in \`Girth/FiniteTraceMaximal.lean\`: \`Set.Finite.exists_maximal_wrt\` does not exist at the pinned Mathlib source. The existing theorem is \`Set.Finite.exists_maximalFor\`, which returns reverse inclusion (not equality). This was corrected. Exact Mathlib source checked at pin \`5bd58ac291422a21f412ae354c91e7d172255a2c\` via the pinned partite-construction manifest. Cardinality theorem signatures were also changed to \`Nat.card\` and local \`Fintype.ofFinite\` instances, avoiding implicit subtype-\`Fintype\` synthesis in theorem statements.

New proof decomposition:
- \`Girth/ForestTraceMissingFaces.lean\`: direct missing-face version of join-tree Helly, for **original indexed bags**.
- \`Girth/ForestTraceLocalCompletion.lean\`: \`HasInternalJoinTreeCompletions\` quantifies over original finite index subfamilies and completions \`N ⊆ S\`; it forbids invented bags. \`exists_original_bag_covering_faces_of_card_ge_three\` uses ≤|K| selected missing faces and the locally completed join tree to force one original bag containing K, with the required third vertex proved from \`3 ≤ K.card\`.
- \`Girth/FiniteTraceConformalLocal.lean\`: \`pairCliqueOn_contained_of_local_completion\` argues by strong induction on a nonempty finite clique: sizes 1 and 2 use vertex/pair coverage; sizes ≥3 use original members covering every deletion face, and the previous Helly lemma. \`traceConformal_of_local_completion\` transfers this to the actual pair graph on \`Z\`, with budget \`Z.ncard ≤ q\`. Thus the **conformality** half of the local-to-global proof now has a complete mathematical decomposition in Lean source, not a postulated \`TraceConformal\` hypothesis.

This is substantial but **NOT a compiled certificate**: no Lean toolchain is available locally and no paid GitHub Actions were requested. \`#check\`/\`#print axioms\` for the new declarations are present in \`CheckTrack8LeafCharging.lean\` but unexecuted. Actual compilation may expose additional tactic/elaboration problems.

**Remaining combinatorial bottleneck:** bounded internal completions force chordality of the trace pair graph; from chordality and the now-proved-source conformality, construct a finite join tree of *distinct maximal nonempty trace sets*, discharging the explicit \`hTree\` of the sharp \`selected.ncard ≤ Z.ncard\` result. The final structural consequence still needs the actual outer construction (Tracks 2 and 7). The manuscript already contains the corresponding correct written chordality/clique-tree proof. No validation marks promoted.

## 14 November further continuation — exact original-index completion and direct conformality

Two new Lean source modules extend the pipeline:

* \`Girth/ForestTraceMissingFaces.lean\` proves a direct missing-face Helly reduction, first for any join tree and then for a finite join-tree completion indexed by **original cover members**.
* \`Girth/ForestTraceLocalCompletion.lean\` defines \`HasInternalJoinTreeCompletions F q\` on original finite index subfamilies. It requires every nonempty selected \`N\` of size ≤ q to be included in an original-index \`S\` admitting a join tree. Its missing-face lemma takes at most |K| deletion-face indices, all in the original cover. \`exists_third_vertex_of_card_ge_three\` discharges the three-vertex separation for |K| ≥ 3.
* \`Girth/FiniteTraceConformalLocal.lean\` contains a full written Lean source argument: by strong induction on a nonempty finite pair clique K of size ≤ q, cover it by a single original member. The |K|=1 case uses coverage, |K|=2 uses a pair-graph edge witness, and larger K use inductively covered deletion faces and the local join-tree/Helly step. \`traceConformal_of_local_completion\` then transfers the result to the pair graph on \`Z\` when \`Z.ncard ≤ q\`.

The new declarations are added to \`CheckTrack8LeafCharging.lean\` for future **exact-head #check and #print axioms**. **These proof scripts have NOT been elaborated by Lean**. No marker can be promoted until they compile and their transitive axioms are inspected.

Independent local Python exhaustive diagnostic \`checks/track8_local_conformality_bounded.py\` checks all distinct-nonempty-subset covers on each universe n≤4, selects the face witnesses of the smallest uncovered clique, and verifies that no original-cover join-tree completion exists for those selected indices. Actual results:

| n | covers | nonconformal covers | explicit missing-face obstructions | false join-tree completions |
|---:|---:|---:|---:|---:|
|1|1|0|0|0|
|2|5|0|0|0|
|3|109|8|8|0|
|4|32297|10576|10576|0|

For n=4 the uncovered minimal clique has size 3 in 9552 cases and size 4 in 1024 cases. All chosen obstructions use ≤|K| original members. The bounded check supports **only** the finite diagnostic, not the general theorem.

A concrete Mathlib API repair was made in \`FiniteTraceMaximal\`: use \`Set.Finite.exists_maximalFor\`, not nonexistent \`exists_maximal_wrt\`; the theorem's conclusion is a **reverse inclusion**, not equality. Source compatibility was compared against the pinned Mathlib tree \`5bd58ac291422a21f412ae354c91e7d172255a2c\`. Cardinality proof declarations now explicitly create finite subtype instances and use \`Nat.card\` at interfaces.

**Remaining pure combinatorics**: (a) exclude chordless cycles in the trace pair graph under the same bounded local-completion premise, (b) construct the finite maximal-clique join tree of a chordal graph and transfer it to distinct maximal original traces. The sharp |Z| selection theorem is already source-proved **under that join-tree input**. The actual structural extraction remains dependent on Tracks 2 and 7.

The PR is draft and unverified; the container has no Lean/lake/elan and DNS access was unavailable, and no paid Actions run was requested. No validation marks were promoted.

## Final pass of 14 November — chordality preparation and integrity checks

\`Girth/FiniteTraceSimplicial.lean\` now gives the first geometric proof step for chordality: \`JoinTree.private_leaf_occurs_only\` shows a vertex in a leaf bag but outside its parent occurs nowhere else, and \`tracePairGraph_private_leaf_simplicial\` proves that its neighbours in the trace pair graph form a clique. This isolates the exact leaf-elimination mechanism needed to exclude induced chordless cycles. **It does not yet prove the global chordality theorem.**

A connector-based whole-branch static audit of the 10 new \`Girth/*.lean\` proof modules plus \`CheckTrack8LeafCharging.lean\` reports:
- 11 files, 1,422 source lines, 30 theorem declarations;
- no explicit \`sorry\`, \`admit\`, \`sorryAx\`, \`axiom\`, \`unsafe\` or \`opaque\` in proof bodies;
- all local Girth import names in this new module collection resolve to either another new file or a known pre-existing source;
- no internal import cycles, balanced delimiters.

**WARNING:** none of these static properties establishes successful Lean elaboration or absence of transitive axioms. The pinned Lean runtime was not installed, and no exact-head CI was run. Retain all validation marks as open pending a real compilation and \`#print axioms\` audit.

The manuscript trace-proof simplification and bag-union qualification were already merged in manuscript PR #453; no additional manuscript changes are necessary for this stage. The remaining mathematical work is the global leaf-elimination/no-induced-cycle proof and finite chordal maximal-clique join tree.

## 15 November: direct cyclic-pair obstruction and constructive clique-tree route

The manuscript's chordality proof has now been simplified in draft [girth PR #463](https://github.com/janhubicka/girth/pull/463): instead of assuming the general theorem that bag-pair graphs are chordal, it deletes join-tree leaves while preserving coverage of the selected edges of an induced cycle. Each cycle endpoint is also covered by a different required edge, whose containing bag cannot be the leaf; running intersection puts the endpoint in the parent. After repeated deletion a single bag would cover two cycle edges, contradicting the induced-cycle assumption. This is elementary and avoids additional terminology.

New Lean source files on this branch:
- \`Girth/ForestTraceCyclicPairs.lean\`: direct recursively decreasing join-tree leaf-deletion proof \`JoinTree.no_cyclic_unique_pairs\`. Hypotheses are a finite set of required pairs, a second required pair through each endpoint, pair coverage, and the prohibition of a bag covering two different pairs.
- \`Girth/ForestTraceLocalChordless.lean\`: \`no_cyclic_unique_pairs_of_internal_completion\`. Chooses ONE ORIGINAL member witnessing each required pair, uses the original-index budget \`Finset.card_image_le\`, invokes \`HasInternalJoinTreeCompletions\`, and applies the preceding no-cycle theorem. It does **not** introduce any additional bags outside the cover.
- \`Girth/FiniteTraceChordlessPattern.lean\`: \`CrossPairNonedge\` and \`no_bounded_chordless_pair_pattern\`. If the four endpoints of two distinct required graph edges contain a nonadjacent pair, they cannot lie together in any original bag. This translates the trace-pair graph to the no-double-coverage interface.
- \`Girth/FiniteTraceSuccessorCycle.lean\`: \`no_bounded_chordless_successor_cycle\`, with edges \`{v e, v (next e)}\` indexed by a fixed-point-free successor permutation. The previous required "other edge through each endpoint" hypotheses are supplied by \`next e\` and \`next.symm e\`, without arithmetic on \`Fin n\`.
- \`Girth/FiniteTraceEliminationBags.lean\`: explicit definition of a perfect elimination ordering; proof that each bag \`{v} ∪ {later neighbours of v}\` is a clique and every nonempty clique is contained in the bag of its earliest vertex.
- \`Girth/FiniteTraceEliminationParent.lean\`: least later-neighbour parent, its order/adjacency properties, and \`laterNeighbor_mem_parentBag\`: every later neighbour \`x\` in the bag at \`v\` also occurs in the bag at the chosen parent. This is the local running-intersection mechanism for the constructive clique-tree algorithm.

**Remaining exact adapters (still OPEN):**
1. Convert an ordinary induced chordless cycle / Mathlib \`SimpleGraph.Walk\` on \`Z\` into the fixed-point-free finite successor-permutation certificate and its cross-pair nonedges. This is the sole remaining interface to conclude ordinary graph chordality from the new combinatorial obstruction.
2. From finite chordality, construct a perfect elimination ordering (finite chordal graph / Dirac simplicial-vertex theorem). This is **not** available as an immediately reusable theorem in the pinned Mathlib source.
3. Construct the forest of parent arcs, connect its components, and prove running intersection from \`laterNeighbor_mem_parentBag\`. Every maximal clique occurs among the elimination bags. Delete nonmaximal and duplicate bags using the existing \`JoinTree.nonempty_eraseMember_of_full\` / \`ForestTreeRewire\` theorem; this yields a join tree of distinct maximal cliques.
4. Transfer the resulting join tree to \`maximalTracePiece\` using the already drafted conformality-to-clique adapters, then discharge \`smallTrace_selection_of_maximalJoinTree\`.
5. Combine the full small-trace statement with the ACTUAL outer forest-extension theorem (numbered Tracks 2 and 7), and check induced relational extraction and nullary values.

The new direct chordless obstruction was independently tested for induced cycles of lengths 4 through 9: each cycle edge must be an original bag, and any original bag restricted to the cycle is either a singleton or one of those cycle edges. For every choice of additional singleton bags, no running-intersection join tree exists: 16, 32, 64, 128, 256, 512 candidates respectively; all zero completions. Reproducible in \`checks/track8_chordless_cycle_bounded.py\`. **Bounded diagnostics do not prove the theorem.**

The branch's \`CheckTrack8LeafCharging.lean\` has been extended with \`#check\` and \`#print axioms\` for the new declarations. No Lean compiler or Mathlib caches exist in the current container, and DNS to github.com is unavailable. **All new proofs remain uncompiled source drafts, no markers promoted, and no paid Actions invoked.** Existing checked rewiring facts may be reused under their exact premises without re-formalization.
