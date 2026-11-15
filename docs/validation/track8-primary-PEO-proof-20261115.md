# Track 8 — minimal proof path after direct PEO counting
Date: 15 November 2026

**Status:** source-level proof decomposition, NOT a fresh Lean kernel certificate. Manuscript draft PR: https://github.com/janhubicka/girth/pull/467. Lean draft PR: https://github.com/janhubicka/lean-girth/pull/1068. Track issue: #1059.

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

The former maximal-clique join tree, parent forest, deletion of nonmaximal/duplicate bags and private leaf charging are NOT necessary for the counting proof. The old conditional join-tree counting segment was removed from FiniteTraceMaximal.lean (142 lines removed), leaving original-index maximalization and representative selection. Optional historical proof sources remain available but are not imported by the focused primary gate.

The remaining graph-theoretic requirement is finite chordal graph => perfect elimination ordering. The pinned Mathlib source has no ready-made theorem for this project. It may be proved via Dirac's simplicial-vertex theorem and finite induction, but it must not be inserted as an unapproved axiom.

## Independent exhaustive check

The reproducible check in checks/track8_peo_cliquetree_bounded.py enumerates every simple graph on up to 6 labelled vertices. Among 6-vertex graphs:
- 18,154 are chordal (greedy elimination succeeds), 14,614 are nonchordal;
- for EVERY maximal clique K of each chordal graph, the elimination bag at K's earliest vertex equals K, and these earliest vertices are pairwise distinct;
- optionally it also verifies parent-forest running intersections, arbitrary links of component roots and deletion of contained/duplicate bags. 4,852 chordal 6-vertex graphs have disconnected parent forests.

An equivalent local checker was executed independently and reproduced all counts. This finite diagnostic is NOT a proof.

## Verification and remaining dependencies

- The existing Mathlib maximality API was corrected to Set.Finite.exists_maximalFor (pinned Mathlib), which gives reverse inclusion, not equality. Nat.card and explicit finite subtype instances are used.
- CheckTrack8Primary.lean deliberately imports only the primary route, avoiding optional uncompiled geometric modules.
- No local Lean/lake/elan executable or Mathlib cache exists in this container. Public GitHub DNS resolution fails locally. No kernel elaboration or executed #print axioms has occurred.
- A standalone pdflatex draft-mode syntax check of the 9-line manuscript replacement succeeded, exit 0. This is NOT a full-paper build.
- Manuscript labels lem:smalltraces and cor:smallrelational remain open. The latter also depends on genuine outer forest-extension witnesses from numbered Tracks 2 and 7 and the induced relational adapter.
