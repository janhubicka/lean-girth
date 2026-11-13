# Track 8 — small traces and induced extraction (13 November 2026)

**Exact original target:** janhubicka/girth, merged manuscript commit 8c9cfa6eb6d817a08f3009fe048fc0be07426ece, original reachable-source SHA-256 45236791f392ca90546dd40f9e9de1d2be9e32bda82b2b26ebb7efc2b5b532ec. Work issue: #1059. The clarification branch revision/track8-small-traces-20261113 changes manuscript source; **do not** reuse the original digest as the changed-branch digest.

**Labels:** lem:smalltraces, cor:smallrelational, thm:main, cor:hyperlocal, cor:partialforest. Sources: paper/06-consequences.tex, paper/05-local-tree-construction.tex, paper/04-local-forests.tex and paper/01-introduction.tex.

This records a written proof/interface audit and bounded diagnostics. It is **not** an exact-head Lean kernel certificate.

## 1. Trace lemma: mathematical proof check

For a finite cover C of V, s ≥ 1, assume every subfamily of up to max(2,s) cover members has a join-tree completion **using only members of C**. Given Z of size at most s, its pair graph G joins vertices lying together in an original trace.

* A join-tree family's pair graph is chordal. A leaf bag has simplicial private vertices; eliminate these, discard the redundant bag, and induct. Intersecting all bags with a fixed vertex set preserves their running-intersection property.
* An induced k-cycle in G, 4 ≤ k ≤ |Z|, yields k **distinct** original cover members supporting its consecutive edges: a repeated member would introduce a chord. Complete these k members inside C. Restricting the bags to cycle vertices leaves exactly this chordless pair graph, a contradiction.
* If a clique K of G is not contained in an original trace, take an inclusion-minimal one. Then |K|≥3, because C covers vertices and G's edges are trace-supported by definition. For each x in K choose a member containing K minus x. The ≤|K|≤s selected members have an internal join-tree completion. The occurrence subtrees for vertices of K meet pairwise, so subtree Helly gives a member containing K, contradiction.
* Hence the distinct maximal nonempty traces are precisely the maximal cliques of the chordal graph G. A finite chordal graph admits a clique tree (simplicial elimination). Root it. Assign the root any vertex in its clique, and each other clique a vertex absent from its parent; maximality makes this possible. Running intersection makes these assignments injective: the path between two bags sharing a vertex would contain the parent of at least one charged bag. There are therefore at most |Z| maximal traces. Choose one **original** member for each.
* When Z is empty, select the empty family. Do not count the empty trace.

The standard finite clique-tree and subtree-Helly steps still require Lean declarations and exact adapters; the written proof alone must not mark lem:smalltraces Lean-verified.

## 2. Exact induced-relational extraction

The outer construction must retain its **stronger forest-extension property** for actual A/B-copies, with m ≥ max(2,s), not merely theorem thm:main(iv), which provides an embedding into a supported tree. Designated B-copies cover vertices and every positive-arity relation tuple; irreducibility and finiteness identify ambient B-copies with designated copies by carrier.

For nonempty Z, select at most |Z| designated B-copies representing maximal nonempty traces. Invoke the actual-copy forest-extension invariant to add designated copies and obtain a mixed forest N∪X **inside C**. Every tuple of C[Z] belongs to an original designated copy, whose trace lies in the trace of a selected copy, so it also belongs to the union. Conversely the union contributes no new ambient relations. Thus the induced relational structure on Z in the amalgamation union equals C[Z]. The mixed forest has shared-vertex support on each incident B-side; use the existing supported-tree embedding theorem and restrict this induced embedding to Z. For Z empty, use a constituent B-copy and ensure matching nullary truth values.

The induced statement is for the **pre-order-completion** structural witness. Extending its acyclic order can create new copies and does not automatically preserve this claim.

Relevant reusable Lean interfaces:
- Girth/ForestCompletionProperty.lean: quantified finite forest completions by designated pieces.
- Girth/ForestStructuralABCompletion.lean: actual A/B support-piece completion, **conditional** on local construction and geometry.
- Girth/ActualDesignatedSupportBridge.lean: ambient B-copies and exact designated support.
- Girth/MixedForestInduction.lean: mixedForest_embeds_supportedTree_of_bMemberSupport (requires actual forest, support of shared vertices, A→B, two distinct A vertices).
- Girth/SupportedTree.lean: supported attachment constructors; its forgetful tree bridge has no converse.
- Girth/ForestTreeRewire.lean: deletion of one-edge pieces, **not** arbitrary deletion of forest subfamilies.

Required new formal adapters: finite trace family/graph and chordal-clique-tree proof; full outer actual-copy forest completion; positive-arity relation coverage including repeated coordinates; ambient/designated carrier identification; shared-support transfer; induced restriction and nullary values. Track 2 must supply the completed join-tree lifting theorem and track 7 the genuine indexed recursive witness. A conditional forest interface is not the main theorem.

## 3. Hypergraph and order audits

For F with an edge, order F and take the ordered one-edge A. Every ambient hyperedge lies in a B-copy, hence has a complete induced order and is represented by an ordered A-copy. An edge-colouring restricts to a colouring of these **copies**, not arbitrary embeddings of an unordered edge. Forgetting order retains the specified family of F-copies and supported-tree embeddings. Linear F has girth >2, so the induced consequence uses g=2; the edgeless target is a separate case.

## 4. Independent bounded diagnostic

Run: python3 checks/track8_small_traces_bounded.py (standard library only).

It enumerates **all** covers by distinct nonempty subsets of each n-point universe, n=1,2,3,4. For covers with more than n maximal traces, it tests whether every selection of at most max(2,n) members has an internal join-tree completion; joins are checked by maximum-spanning-tree intersection weights. Results:

| n | Covers with >n maximal traces | Locally extendible counterexamples |
|---:|---:|---:|
| 1 | 0 | 0 |
| 2 | 0 | 0 |
| 3 | 0 | 0 |
| 4 | 112 | 0 |

Each of those 112 four-vertex covers has an obstruction using three selected members. **Bounded enumeration is not a proof.**

## 5. Status and promotion gate

- lem:smalltraces: written argument audited; **kernel proof OPEN**.
- cor:smallrelational: logically derived from actual-copy forest-extension plus coverage; **exact Lean adapter OPEN**.
- thm:main: historical supported-tree lemma reusable under printed hypotheses; **track 2 and 7 prerequisites OPEN**.
- cor:hyperlocal and cor:partialforest: copy-versus-embedding colourings checked; inherit the unresolved structural-theorem obligations.

No new validation mark was promoted. Before closing Track 8: pin a fresh source digest of the clarified branch, pin a Lean commit, run local Lean, inspect elaborated assumptions and \`#print axioms\` for every closing declaration; reject sorryAx, extra assumed output invariants and unconstructed witnesses.
