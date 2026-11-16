# Track 8 — minimal proof path after direct PEO counting
Date: 15 November 2026

**Status:** source-level proof decomposition, NOT a fresh Lean kernel certificate. Manuscript PR #467 has **merged**: https://github.com/janhubicka/girth/pull/467. Lean draft PR: https://github.com/janhubicka/lean-girth/pull/1068. Track issue: #1059.

## The new direct route

Let F be the original finite indexed cover, Z the tested vertex set, and q >= |Z|. Every selected nonempty family of <=q original indices must extend to a running-intersection tree **using other original members**. Every vertex of Z occurs in an original bag.

Conformality of the finite trace pair graph follows from the finite clique induction in Girth/FiniteTraceConformalLocal. Induced chordless cycles of length >=4 are excluded by the direct cyclic-pair leaf-deletion argument in ForestTraceCyclicPairs, ForestTraceLocalChordless, FiniteTraceChordlessPattern and FiniteTraceSuccessorCycle. The exact adapter from a graph induced cycle to the successor/cross-pair certificate is still open.

**No clique tree is needed for the sharp count.** In a perfect elimination order, any maximal clique K is the bag consisting of its FIRST vertex v together with all later neighbours of v. The latter form a clique containing K and hence equal K by maximality. Distinct maximal cliques have distinct first vertices. Conformality identifies the maximal cliques with distinct maximal nonempty traces. Therefore the number of maximal traces is at most |Z|.

New source Girth/FiniteTracePEOCount.lean:
- maximalTrace_subset_Z and maximalTraceVertices_nonempty: move maximal traces to actual elements of Z.
- maximalTrace_eq_eliminationBag and maximalTrace_card_le_of_PEO: inject maximal trace types into Z by selecting the first vertex.
- smallTrace_selection_of_PEO: pick ORIGINAL cover indices with selected.ncard <= Z.ncard, including empty case and duplicate-index control.
- smallTrace_selection_of_local_completions_and_PEO: combine derived conformality and the sharp count. The only graph input is an actual perfect elimination order.

These declarations reuse Girth/FiniteTraceEliminationBags.maximalClique_eq_laterNeighborBag and are included in the focused CheckTrack8Primary.lean file with #check and #print axioms requests.

## Obsolete path is no longer a gate

The former maximal-clique join tree, parent forest, deletion of nonmaximal/duplicate bags and private leaf charging are NOT necessary for the counting proof. The old conditional join-tree counting segment was removed from FiniteTraceMaximal.lean (142 lines removed), leaving original-index maximalization and representative selection. The superseded optional modules (leaf charging, elimination-parent forest/occurrence and private-leaf simpliciality), the old sprawling check gate, the optional old diagnostics and the 2026-11-14 exploration ledger were **deleted from this draft PR**. Their earlier versions remain accessible through Git history. This cleanup removes hundreds of lines of uncompiled dead-end work. The primary import stack retains only source files actually used by the direct argument.

The remaining graph-theoretic requirement is finite chordal graph => perfect elimination ordering. The pinned Mathlib source has no ready-made theorem for this project. A concrete clique-minimal-separator / two-nonadjacent-simplicial-vertices proof is in docs/validation/track8-dirac-separator-proof-20261115.md; the elementary Lean lemmas are in Girth/FiniteTraceSimplicialCriterion.lean. The full Dirac theorem and finite PEO construction remain unformalized and must not be inserted as axioms.

## Independent exhaustive check

The reproducible, trimmed check in checks/track8_peo_count_bounded.py enumerates every simple graph on up to 6 labelled vertices. Among 6-vertex graphs:
- 18,154 are chordal (greedy elimination succeeds), 14,614 are nonchordal;
- for EVERY maximal clique K, the elimination bag at K's earliest vertex is exactly K; these vertices are pairwise distinct.
- the separate checks/track8_dirac_separator_bounded.py tests the exact strong-Dirac clique-separator induction on all 18,153 noncomplete chordal six-vertex graphs, with zero failures.
An equivalent local checker was executed independently and reproduced all counts. This finite diagnostic is NOT a proof.

## Verification and remaining dependencies

- The existing Mathlib maximality API was corrected to Set.Finite.exists_maximalFor (pinned Mathlib), which gives reverse inclusion, not equality. Nat.card and explicit finite subtype instances are used.
- CheckTrack8Primary.lean deliberately imports only the primary route and the elementary simplicial criterion. CheckTrack8AllDependencies.lean lists every theorem in its transitive new source modules with both #check and #print axioms for later exact-head verification. Neither file has been executed.
- No local Lean/lake/elan executable or Mathlib cache exists in this container. Public GitHub DNS resolution fails locally. No kernel elaboration or executed #print axioms has occurred.
- A standalone pdflatex draft-mode syntax check of the 9-line manuscript replacement succeeded, exit 0. This is NOT a full-paper build.
- Manuscript labels lem:smalltraces and cor:smallrelational remain open. The latter also depends on genuine outer forest-extension witnesses from numbered Tracks 2 and 7 and the induced relational adapter.

## Current remaining gate

An induced chordless cycle must be converted to the exact cyclic-pair/successor certificate used by the new direct obstruction. The standard finite chordal-to-PEO theorem must then be proved from a simplicial-vertex argument. The latter is supported by the written strong Dirac induction and bounded diagnostics, but it is **not a Lean-certified theorem**. No clique-tree construction is needed. No validation marker has been promoted.


## 15 November afternoon — exact end-to-end verification route

The retained proof stack is 17 Girth modules with 44 source theorem declarations. The static source review found no explicitly written sorry/admit/axiom/unsafe/opaque, no missing local import, and balanced delimiters; it does NOT establish Lean elaboration. The current revision provides:

- Girth/FiniteTraceSimplicialCriterion.lean: precise simplicial-in-an-induced-subgraph condition, PEO equivalence and the elementary clique-separator Dirac induction sublemmas.
- Girth/FiniteTracePEORank.lean: construct an actual LinearOrder from an injective numerical elimination ranking using Mathlib LinearOrder.lift'. The remaining PEO task is obtaining such a ranking from Dirac's simplicial witness.
- Girth/FiniteTraceFinRotateCycle.lean: specialize the chordless-cycle obstruction to finite cyclic indices using Mathlib finRotate, with fixed-point-freeness derived from the pinned support_finRotate_of_le theorem. The outstanding adapter is the graph-specific CrossPairNonedge data for a standard induced graph cycle.
- docs/validation/track8-dirac-separator-proof-20261115.md: a complete English minimal-clique-separator induction establishing the strong Dirac theorem, with explicit path/cycle formalization subgoals and an adversarial counterexample to the tempting longest-induced-path shortcut.
- checks/track8_dirac_separator_bounded.py: exhaustive strong-Dirac separator diagnostic on all simple graphs up to six vertices; all 18,153 noncomplete chordal six-vertex graphs pass.
- checks/track8_peo_count_bounded.py: direct earliest-vertex PEO counting checker (the optional parent-forest construction no longer appears in the source).
- checks/run_track8_primary_local.sh: reproducible local Lake build of the actual primary modules, followed by CheckTrack8Primary.lean and CheckTrack8AllDependencies.lean. It deliberately fails if Lake is unavailable. The full gate requests #check and #print axioms on all 44 retained source theorems.

The older optional uncompiled clique-tree construction, private-leaf charging, its expansive check file and old diagnostic have been deleted from the PR. This reduces review and compilation scope while preserving the source history through prior commits.

**No Lean build or executed #print axioms has succeeded in this runtime; no theorem is being promoted to verified.** Current manuscript PR #470 adds review-only open markers to thm:main, cor:hyperlocal and cor:partialforest, in addition to the existing open small-trace and small-relational marks. The normal circulation PDF text is unchanged.


## 16 November — replace per-edge nonedge cases by a triangle-free certificate

A further simplification of the remaining cycle adapter is now present
in Girth/FiniteTraceTriangleCycle.lean and
Girth/FiniteTraceCycleCertificate.lean.

For a cyclic pair family (a,b) indexed by E, it is unnecessary
to explicitly choose a nonadjacent pair among the endpoints for
each pair of distinct required edges. It suffices to establish:

1. The unordered two-element edge sets are pairwise distinct.
   Since each required edge has two distinct endpoints, the second
   edge has an endpoint z absent from the first.
2. The graph INDUCED on the cycle vertices is triangle-free
   (the Mathlib predicate SimpleGraph.CliqueFree 3).
   The ambient trace graph need not be triangle-free.

If both endpoints of the first edge were adjacent to z, the
three vertices would form a triangle. Thus at least one of
those two pairs is a nonedge, giving precisely the original
CrossPairNonedge certificate. The source now factors this
through distinct_two_pairs_have_third,
triangleFreeOn_of_induced_cliqueFree,
crossPairNonedge_of_induced_cliqueFree, and the direct
no_bounded_fin_cycle_of_triangleFree wrapper.

**Pinned Mathlib API discovery:** SimpleGraph.cycleGraph k is already
defined in Mathlib/Combinatorics/SimpleGraph/CycleGraph.lean, with
cycleGraph_adj' and cycleGraph_neighborSet at the pinned revision.
Likewise finRotate and support_finRotate_of_le are already available.
The remaining induced-cycle bridge should use a copy of
cycleGraph k for k >= 4 and prove ONLY edge-set injectivity and
CliqueFree 3 of the induced cycle graph, avoiding another ad hoc
modular successor implementation.

The elementary finite certificate was independently checked for every
k=4,...,100: all consecutive edges were distinct, no triangle
occurred, and every two different edges had the required cross
nonedge. The three-cycle is intentionally excluded:
cycleGraph_three_eq_top shows the triangle negative control.
Reproduce with python3 checks/track8_cycle_triangle_certificates.py.

**Status:** New source lemmas have no explicit sorry/admit/axiom
but have NOT been Lean-compiled. Neither the full small-trace theorem
nor the structural consequences have a new validation certificate.
The other graph-theoretic gate remains finite chordal graph => PEO
via the documented strong Dirac minimal-separator induction.
Final structural extraction still needs the actual Tracks 2/7
forest-extension witnesses.
