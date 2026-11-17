# Track C — completed ordered W and selected source interface (16 November 2026)

## Verified-by-inspection dependency audit, NOT Lean kernel certification

Branch: `validation/5-filling-cutoff-two`.

The earlier `realColouredFirstWagon_privateEHN` feeds the RAW `firstWagonDisjointUnion` to ordered EHN. This is not the required induced relational source whenever two summands have vertices of the same unary colour. The raw binary relation omits their comparisons. This is a genuine obstruction, not solved by installing an auxiliary `LinearOrder`.

The correct relational source is `completedFirstWagonColouredUnion`: its k-edges remain the tagged component edges, while its binary relation compares same-colour vertices across summands.

## New source candidate

`TrainFillingPrivateCompletedWCopyLocality.lean` proves `completedFirstWagon_ACopy_in_one_summand` *conditionally on successful elaboration*. Every embedding of the genuine small `colouredOrderedEdgeSource` into the completed W sends the source spanning k-edge to a target k-edge; the existing `completedFirstWagon_edge_in_one_summand` then locates all source vertices in one summand. No extra hyperedges arise from completing within-colour comparisons.

A `#print axioms` probe is registered in `Girth/CheckTrack5Private.lean`. This branch and its new theorem remain uncompiled.

## Exact next proof, before EHN can be called

1. For each first wagon `F_p = D.induce (oldCarrier p)`, construct its vertex inclusion into completed W and prove `map_rel_iff` for ALL symbols: the k-ary hyperedge, unary colours and binary within-colour order. The last clause needs the actual source colour-block order and the order key of completed W. Merely checking k-edge support is insufficient.
2. Use A-copy locality plus factorization through the *induced* F_p to derive `ALinear A W` from local A-linearity. Establish A-strongness of every F_p inclusion without assuming the desired EHN witness.
3. Prove the ordered EHN selection statement on completed W, retaining an actually increasing selected W-copy and a common monochromatic selected A-edge family. Track 1's newly merged generic selected EHN infrastructure may supply the universal EHN input, but does not automatically identify these particular W relational presentations.
4. Apply the marked allowed-A_1 and covered-X owner splitting with a genuine full induced selected family. Mainline Track 1 has recent checked intermediate selected-EHN lemmas; the full assembled coloured witness remains draft and requires its own exact-head build.
5. Only afterward instantiate the concrete `SummandPrivateTemplate.fromSelectedUnion` edge equivalence and the shorter *unrestricted* ordered `RR_h` on the actual M (which need not have a well-defined fine X-position part map). The direct one-map edge train and two-edge-type target girth routes can then be reused.

## Review constraints

- Do not use the raw union for the completed-order EHN embedding.
- Do not confuse auxiliary order with binary relational order.
- Do not replace the unrestricted shortened Ramsey theorem by the incorrect X-position-partite version.
- Keep the original and shortened edge types distinct.
- No proof is validated merely because `#print axioms` commands are present.
- The new source should stay draft until exact-head Lean elaboration and strict axiom checks finish.
