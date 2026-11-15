# Track 4 — actual q=2 coreCoverage obstruction (15 November 2026)

**Status: adversarial mathematical obstruction to an overstrong field in the current conditional q=2 attachment interface.** This is NOT a counterexample to the circulation forest lemma or the implication F_t => R_t; it shows that the existing generic `ActiveAttachmentBounds.coreCoverage` cannot be deduced from its previously proposed q=2 local inputs. No draft theorem or validation mark should be promoted from those inputs.

## An explicit nine-vertex example

Work in the ordinary undirected graph language. Let the irreducible coloured edge structure `A=K4` have four vertex parts 0,1,2,3. Consider vertices with parts:

| part 0 | part 1 | part 2 | part 3 |
|---|---|---|---|
| a,u | b,z | c,x | y,w,v |

Let `R` be the graph obtained by taking the union (all pairs within each set) of the following **three physical K4 copies**:

- `H_ab={a,b,x,y}` with parts 0,1,2,3;
- `H_ac={a,z,c,w}` with parts 0,1,2,3;
- `H_bc={u,b,c,v}` with parts 0,1,2,3.

These are the **only** K4 subgraphs of R (verified by exhaustive enumeration of all nine-vertex subsets of size four). Thus the full physical A-support hypergraph consists precisely of H_ab,H_ac,H_bc. Any two of them intersect in exactly one vertex: respectively {a},{b},{c}. In particular its physical support girth is >2 (there is a Berge 3-cycle, permitted at cutoff two), and R is A-generated: every vertex and every graph edge belongs to one of the three physical K4 copies.

The part map above makes R **A-partite in the underlying relational graph language**: every irreducible induced subgraph is a clique; because R has no edges within a part, such a clique contains at most one vertex per part, and hence its projection to K4 is an induced embedding.

However `S={a,b,c}` is itself an irreducible triangle in R. Its three graph edges belong to three different physical K4 copies:
- ab belongs to H_ab;
- ac belongs to H_ac;
- bc belongs to H_bc.

No K4 copy contains all three vertices. Hence `IrreduciblesExtendTo K4 R` is **false**, despite A-generation, A-partiteness, support girth >2, and every physical pair of K4 copies having allowed (singleton) overlap.

The cutoff-two **finite mixed SET forest** also holds with one designated complete support member B=R: the family consists of the full three-edge support of B and the three ambient one-edge support pieces. Every pair of different members meets in a single vertex or in a complete physical K4 edge of both members; for a designated B support and a one-edge piece, their intersection is that physical edge. Thus the finite-set mixed forest property through two is satisfied.

## Exact Lean implication which fails

The checked `ForestTailStage.trueActive_irreduciblesExtendTo` and ordered specialization `orderedTrueActive_irreduciblesExtendTo_of_nontrivial` require `3 ≤ t.headD 0`; this is essential, not a mere proof limitation. Their shadow-clique argument uses support girth >3 to exclude triangle cycles assembled from different A-copies. The counterexample above shows that replacing that numerical hypothesis by `2 ≤ t.headD 0` is invalid, even for a relational A-partite, A-generated, physically linear graph.

At q=2, `ActiveAttachmentBounds.coreCoverage : IrreduciblesExtendTo A E.toRelStructure` is stronger than the consequences of same-q finite mixed forests and local partiteness. It is used in `Girth/TrainSelectedPictureStageAssembly.lean` to establish `supportCovers`, `supportNonempty`, and `mixedCoverage` for the assembled output stage.

The separate new universal-top proof `activeGluingWitness_top_fullSystemGirth_two_of_finiteMixed` may supply the requested `ActiveAttachmentBounds.cutoffTwo` field, but it does **not** discharge `coreCoverage` and cannot fix this mismatch.

## Repair options to investigate (NOT established)

1. **Preferred:** replace the q=2 use of the overstrong A-irreducible-core-coverage condition by the **actual mixed A-or-selected-B irreducible coverage** needed for output `ForestTailStage.mixedCoverage`, plus physical A-support coverage for core vertices. Prove the corresponding concrete q=2 attachment constructor, retaining all original selected labels and physical edges.
2. Alternatively, prove a special q=2 finite picture-step theorem directly without invoking the generic `ActiveAttachmentBounds.coreCoverage` field. It may reuse the new genuine bottom forest preservation and universal-top order-two lemma. The original strong selected B-copy and train reflection must still be retained.
3. Do NOT simply add `IrreduciblesExtendTo A E` to the F_2 witness statement or infer it from A-partiteness and girth >2: the explicit graph R above refutes that inference.

**Ordered-language caveat:** The finite counterexample is constructed in the underlying relational graph language. The current ordered PartiteConstruction API must be audited for its exact treatment of the added order relation in irreducibility and source-to-part projection. This caveat does not make the missing q=2 inference valid; it identifies the exact model translation required before a formal Lean counterexample is asserted.

## Finite independent check

An exhaustive local Python enumeration confirmed:
- Nine vertices and exactly three actual K4-copy carriers;
- Pairwise overlaps `[1,1,1]`;
- Every graph adjacency joins different assigned parts;
- Exactly one K3 clique not contained in an actual K4, namely `{a,b,c}`.

The check is a finite combinatorial audit, NOT a Lean kernel proof.

**No CI, no merge, no marker promotions.** The q=2 active-core-coverage gate must remain open until an actual repaired constructor/argument is formalized and kernel checked.
