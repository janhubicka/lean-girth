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


## Strong-copy no-go: adding ambient A-copies cannot repair this

The obstruction is stronger than failure of one abstract implication. Suppose an E has total IrreduciblesExtendTo A E and the problematic R above embeds into E as an A-strong induced copy b. Total core coverage would give a physical A=K4 copy in E containing the mixed irreducible triangle b({a,b,c}). Its intersection with b(R) contains at least two distinct vertices. A-strongness of b forces the entire K4 carrier inside b(R). Since b is induced, this factors back to an A=K4 embedding inside R containing {a,b,c}, contradicting the explicit enumeration. Hence **no such A-strong completion E exists** for this target, even if E is allowed to add arbitrarily many vertices and physical A-edges.

The general mathematical statement is independent of graphs: for any A-strong induced embedding b:B→C, if C has total irreducible A-extension, then every irreducible induced subset of B containing at least two distinct vertices already lies inside an A-copy of B. This is developed as a source-only Lean candidate in Girth/TrainAStrongIrreducibleReflection.lean, with theorems irreducible_two_point_extension_reflect_of_aStrong and no_aStrong_covered_extension_of_irreducible_obstruction. It is NOT yet Lean-compiled.

**Consequence for q=2 repair**: one cannot repair the F_2 witness by merely adding outside A-copy completions while keeping its selected target copies A-strong. Either bypass/relax the generic ActiveAttachmentBounds.coreCoverage field at q=2 (prove the exact weaker selected A-or-B mixed coverage actually required), or design a separate base-case construction with different treatment of selected copy images. Do not silently require an impossible extra strong completion from F_2.


## Essential distinction: F_2 assertion versus selected ForestTailStage

The actual circulation definition of F_t (paper/10-cycle-conditions.tex, def:principles) promises only: (i) a physical-edge Ramsey family, (ii) bounded mixed support forests, (iii) original part/intersection parameters and positive proper-cut full system bounds, with one selected embedding per image. It EXPLICITLY does not require selected copies to cover all vertices, and it does NOT state that every irreducible lies in a selected local-target copy or an ambient A-copy.

The new TrainSelectedMixedCoreAttachment and TrainActualSelectedMixedCoreAttachment theorems are mathematical CONDITIONAL interfaces from a genuine selected lower ForestTailStage: that stronger stage has the extra mixedCoverage field, which supplies precisely the selected active-target-or-A local core alternative. The new ActiveAttachmentMixedBounds and actual mixed-core OrderStage picture-step constructor use that field.

**But one must not substitute an arbitrary F_2 witness for that selected lower ForestTailStage.** The stated F_2 forest/arrow/parameter conditions do not imply the stage's mixedCoverage. In particular, a finite F_2 witness may be enlarged by a disjoint A-support component containing an irreducible piece assembled from several A-copies, with no additional selected local-target copy covering it. Such a component does not disturb an existing selected Ramsey family; at cutoff two pairwise A-support intersections may remain singleton (as in the K4 triple example), so the mixed two-forest property survives. Thus mixedCoverage cannot be silently inferred from F_2.

**Recommended proof fork:**
1. For a recursive lower construction that really produces a selected ForestTailStage, reuse the nested mixed core and mixed attachment constructor, even at q=2.
2. For the STANDALONE circulation implication F_t=>R_t from an arbitrary F_t witness, investigate a WEAKER forest-to-order intermediate stage that omits mixedCoverage (R_t does not request it); preserve the actual strong selected copies, complete support, full train restrictions, forests, system girth and parameter fields. Reuse finite picture combinatorics after factoring them away from the overstrong stage invariant, or prove a separate q=2 base operator with hypotheses F_2 really supplies.
3. Do NOT claim the current mixed-core stage wrappers close unconditional F_2=>R_2. They close a conditional selected-stage interface.

No marker changes or kernel certificate.
