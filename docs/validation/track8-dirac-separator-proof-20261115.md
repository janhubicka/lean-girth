# Track 8: finite chordal graph to perfect elimination order
Date: 15 November 2026

## Status and objective

This is a complete **ordinary mathematical proof plan** for the last graph-theoretic step of the direct small-trace argument. It is **NOT** yet a Lean elaboration or kernel certificate. Do not replace the missing result by an axiom or promote manuscript validation marks.

The target is the following standard finite chordal graph theorem: if a finite simple graph has no induced chordless cycle of length at least four, its vertex set admits a perfect elimination order (PEO). A PEO orders vertices so that, for every vertex v, its neighbours later than v form a clique. The primary Track 8 theorem in Girth/FiniteTracePEOCount.lean proves the exact selected.ncard <= Z.ncard bound once this PEO is given.

## Step 1: minimal separators are cliques

Let G be chordal and a,b nonadjacent. Choose an inclusion-minimal vertex set S disjoint from {a,b} such that a,b belong to distinct connected components of G-S. The choice exists: deleting all vertices other than a,b separates them, and finite sets have inclusion-minimal separators.

Let A and B be the two components of G-S containing a and b. For every s in S, the minimality of S implies that a,b become connected in G-(S-{s}). The connecting path must pass through s and therefore s has a neighbour in A and in B. In particular both A and B are nonempty.

Suppose s,t in S were nonadjacent. In A together with s,t choose a shortest s-t path with all internal vertices in A; it exists because s,t each meet A and A is connected. Choose another such shortest path with internal vertices in B. Both paths are induced, their internal vertices lie in different components of G-S and have no cross edges, and s,t themselves are nonadjacent. Their union is an induced cycle of length at least four, contradicting chordality. Thus S is a clique, including the empty-separator case.

**Formalization subgoals:** finite existence of an inclusion-minimal separating S; minimum-separator-neighbour lemma; shortest induced paths with internal vertices in a specified component; union of these paths gives the precise finite induced-cycle certificate used by ForestTraceLocalChordless and FiniteTraceSuccessorCycle. In particular, distinguish an induced cycle from a merely closed walk.

## Step 2: strong form of Dirac's simplicial theorem

Induct on the number of vertices of an induced chordal graph H. The strengthened claim is: H is complete, or it has **two nonadjacent simplicial vertices**. (An empty or singleton graph is complete.)

When H is not complete, choose nonadjacent a,b and a minimal separator S as above. Its components A and B contain a and b. Consider the induced subgraphs H_A on A union S and H_B on B union S. They are both strictly smaller than H, and chordality passes to induced subgraphs.

Apply induction to each H_i. If H_i is complete, choose any vertex v_i in its component A or B: it is simplicial within H_i. Otherwise, induction gives two nonadjacent simplicial vertices of H_i. Since S is a clique, at least one lies outside S; it therefore belongs to the indicated component. Pick that one for v_i.

A vertex v_i in A or B has NO neighbours in H outside its component union S. Consequently, if it is simplicial within H_i, it is simplicial in H. The two chosen vertices v_A and v_B lie in distinct components of H-S, so they are nonadjacent. This proves the strengthened claim.

The elementary parts of this argument now have Lean source proofs in Girth/FiniteTraceSimplicialCriterion.lean: clique-neighbourhood characterization, monotonicity under restriction, choosing a simplicial vertex outside a clique S from the two-vertex dichotomy, and transfer from an induced component with no external neighbours.

## Step 3: construct a PEO by deletion

Given any finite induced chordal H, the strong Dirac theorem yields a simplicial vertex v. Delete v; the remaining induced graph is chordal. Inductively choose its PEO and put v first. The later neighbours of v form a clique because v was simplicial. For every other vertex, its later-neighbour set is unchanged from the induced graph. The resulting order is a PEO.

In Lean it is preferable to encode the elimination order as a permutation/rank map of the finite vertex type and lift it to a LinearOrder, rather than postulating a LinearOrder at each deletion step. The equivalence between PEO and simpliciality within each suffix is already in Girth/FiniteTraceSimplicialCriterion.lean.

## Step 4: apply to the trace graph

The existing direct cyclic-pair leaf-deletion proof excludes induced chordless cycles under bounded original-cover join-tree completions. The exact adapter from an induced graph cycle to the successor-permutation and CrossPairNonedge data remains to be checked. Together with Steps 1-3, it supplies a PEO of the trace pair graph. The primary smallTrace_selection_of_local_completions_and_PEO theorem then yields an actual family of <=|Z| ORIGINAL cover members dominating all nonempty traces, with the empty case included.

The remaining noncombinatorial connection is actual forest extension from numbered Tracks 2 and 7 and induced relational restriction.

## Independent adversarial diagnostics

The exact minimal-separator induction was exhaustively checked for every graph of up to six labelled vertices by the Python script checks/track8_dirac_separator_bounded.py:

- Six vertices: 18,154 chordal graphs, of which 18,153 are noncomplete.
- For all 18,153 noncomplete cases, the greedily chosen minimal a-b separator was a clique, every separator vertex had a neighbour in both principal components, and the two strictly smaller induced graphs yielded simplicial vertices outside the separator that were nonadjacent and simplicial in the original graph.
- All PEO and maximal-clique earliest-vertex identities also passed on the same 18,154 chordal six-vertex graphs in checks/track8_peo_count_bounded.py.
- No claim is made for unbounded graphs or for Lean kernel verification; these are independent bounded checks.

**Rejected shortcut:** not every endpoint of every *longest induced path* in a chordal graph is simplicial. A five-vertex counterexample has edges (0,1),(0,2),(0,3),(0,4),(1,2),(1,3). The induced path 1-0-4 is longest, but endpoint 1 is not simplicial (its neighbours 0,2,3 do not form a clique). Do not use that shortcut in the English or Lean proof.

## Acceptance gate

Only claim this theorem Lean-validated after: finite separator and induced-path lemmas compile, the stronger Dirac induction and PEO construction compile, the cycle-certificate adapter compiles, and the resulting small-trace theorem passes exact-head #print axioms (not just local grep for sorry). No paid GitHub Actions were requested.
