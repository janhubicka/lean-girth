# Adversarial audit of the girth circulation formalization

**Date:** 29 October 2026. **Lean baseline:** `3af405cc3a51ca7d3201e221a8a2a56d2e443751`. **Manuscript baseline:** `b043cd03c25e661266be71054ca1fa55ac68991e`. **Audit PR:** #665. Circulation only; no appendix proof is being validated or edited.

## Verdict and limits

The audit did not establish a false theorem or a kernel bypass in the inspected formal proofs. It did find a consequential mismatch in the proposed positive-cut proof interface, stale coverage descriptions, an isolated module needing explicit axiom auditing, and redundant CI work. Several results described as future work already have substantial, checked implementations.

The whole repository received a source/import/export census; the semantic review concentrated on simultaneous replacement, source-label provenance, actual cycle reduction/standard transport, mixed two-standard geometry, parameter transport, forest increment and recursion interfaces. This is **not an independent line-by-line mathematical audit of all 532 modules**. Compilation certifies each stated theorem under its actual premises, not that those premises match an informal application or can all be obtained in the final recursion.

## 1. Correct track A before continuing

In `TrainSimultaneousSupreme.lean`, `BigCycle.ShortValid D C k j e` requires `e ∈ D.edges (C.label k)`, where `k` is an occurrence of the **original** cycle. `PlanValid` keeps occurrences of that same designated label. In contrast, a supreme gluing-copy label in the **reduced witness** identifies an entire attached standard. It does not automatically identify a designated B-copy occurring on the original cycle.

Consequently, the earlier task phrasing “construct ShortValid witnesses into the supreme copy and invoke the fixed-target short-only theorem” skips a genuine identification step. The checked Lean theorem is not wrong; the proposed application is stronger than its available data.

The correct route is:

1. Use the reduced supreme local copy to select a standard.
2. Construct arbitrary physical short replacements moving the cycle into that standard, preserving the connector word. These are not yet replacements relative to a fixed original B-label.
3. Establish legality and acceptability of the new cycle and preserve its order. Retain a designated occurrence in the order-one boundary case.
4. Apply the old bound/zero-cut transport to obtain a supreme **designated B-copy** there.
5. Pull its supremeness back to the original cycle using the existing arbitrary-replacement theorem.

The key forgotten exports are `BigCycle.arbitrary_replacement_complete_of_three_le` in `TrainArbitraryReplacementComplete.lean` and `BigCycle.arbitrary_legal_replacement_all_conclusions` in `TrainArbitraryLegalReplacementComplete.lean`. The first constructs the legal replacement cycle for source length at least three from actual local incidence, long-piece geometry and freshness. The second works at every source length once the literal output is a legal BigCycle and an order-one designated-retention witness is supplied. Both retain the explicit linear-pretrain and geometric premises and transfer a later indexed supreme label back to the original cycle.

The remaining mathematical work is the physical minimum-segmentation construction, including the two-segment/order-one cases, not another abstract global replacement library. `TrainShortOnlyPlanGlobal` remains useful when its original designated target really exists.

## 2. Prevent circular use of wagon geometry

`TrainWagonStrongInduced.parent_eq_of_two_vertices_in_wagon` and `outside_edge_intersection_subsingleton` assume `D.LinearPretrain`. That predicate already includes pairwise linearity of wagon vertex carriers. These results cannot establish output-wagon linearity by first inferring output strongness from that same assumed linearity.

Likewise, the auxiliary cycle used in the manuscript's output-wagon strongness proof is not acceptable: it violates A2. Only the unconditional legal-reduct construction and order inequalities apply to it. The acceptable-reduct theorem must not be invoked before acceptability is independently established. The manuscript already contains a warning for this point; retain it.

This is a restriction on the integration argument, not a discovered inconsistency in those conditional Lean results.

## 3. Results to reuse rather than reprove

| Existing modules | Actual reusable content | Limitation still to discharge |
|---|---|---|
| `TrainSelectedPictureContainedBlocks` | `attachedSelectedPicture_mixed_localize`, `attachedSelectedPicture_containedBlocks_force_core_pairEdge`, `attachedSelectedPicture_contained_cycle_force_core_pairEdge`: actual selected-picture mixed designated/edge block localization and obstruction | Instantiate the real shared-train, old/witness bounds, strongness and physical incidence premises; then finish output geometry. This is not merely an edge-only abstract lemma. |
| `TrainAllAdjacentParametersBridge` | `activeAttached_actualASupport_allAdjacentParameters_of_orderOne`: actual generated A-support adjacent parameters under interior order-one bounds; universal top handled separately | Supply the inductive old/core sibling bounds and shared compatibility. |
| `TrainAllAdjacentParameterPreservation` | Parameter preservation using stronger full-system-girth hypotheses | Do not confuse a supplied full-system bound with a proof that the recursive witness has it. |
| `TrainFillingCarrierInvariant` | Exact filled old-edge carriers, carrier linearity and strong-induced target transport | System-girth under filling remains a separate theorem. |
| `ForestActualDesignatedTrueActiveIncrement` | `actualPartiteDesignatedAB_selectedForest_of_trueActiveOldFull`: actual designated B/ambient A increment without pruning uncovered core edges | Local Ramsey witness existence, actual active generation, old/local forest and girth assumptions remain explicit. |
| `ForestStructuralABCompletion` | Actual structural A/B completion from the local copy-cover interface | Not the whole structural recursion. |
| `ForestJoinLift`, `ForestJoinLiftLinear` | Checked generic local join-tree lifting and linear outer-piece assembly | Instantiate the actual support/intersection data; do not implement a second join-tree library. |
| `TrainCutoffWellFounded`, `TrainCutoffLexRank` | Well-founded multiplicity-lex rank and both recursive rank decreases | The recursive witness-existence theorem is not a consequence of rank decrease alone. |
| `TrainSupremeVertexCoverage` | Vertex-connector coverage by a supreme copy with explicit carrier compatibility; real shared-witness compatibility is also provided | Do not assume carrier compatibility for arbitrary abstract incidence data. |
| `TrainActualZeroCutGlobalSupreme`, `TrainActualStandardPhysicalMap`, `TrainActualStandardStrongFromBase` | Actual one-standard global plan transfer and full-standard pair-edge reflection under explicit strongness | These are checked baseline interfaces, not new targets to reimplement. |

A small `Girth/Circulation.lean` facade makes these endpoints discoverable. It declares no new theorem. Its dependency closure excludes historical experiments, but exclusion from this facade is not a deletion criterion.

## 4. Retire failed routes, keep their counterexamples

**Local replacement validity alone implies global legality — reject.** The definitions correctly retain `PlanProducesBigCycle`. A finite diagnostic has edges `{0,2}`, `{1,3}`, `{0,4}`, `{1,5}`, with the first two in one wagon and the others in separate wagons. Take designated edge families F={first,second}, G={third,fourth} and source cycle `F–0–G–1–secondEdge–firstWagon`. It is a legal acceptable abstract cycle with linear ambient edges and wagon carriers. Local replacements relative to F exist, but their flattened word repeats the first wagon and has adjacent identical second-edge labels; exhaustive enumeration finds no legal global plan. This is a diagnostic for the abstract shortcut, not a counterexample to a checked theorem or a claimed actual partite realization. The diagnostic is Python-checked, not newly Lean-certified.

**A union of individually strong pieces is strong — reject.** In the 3-uniform forest with edges `{0,1,2}`, `{3,4,5}`, `{0,3,6}`, the first two one-edge pieces are individually strong, but their union meets the third in two vertices without containing it. Even a mixed three-member forest does not justify the union inference. The entire gluing image must satisfy the actual strongness premise.

**Pruning uncovered edges preserves higher system girth — reject.** The existing `TrainA2PruningCounterexample` checks that A2 can change even when wagon carriers stay identical. `TrainA2PairShadow` identifies the pair-edge information that matters. Keep these negative regressions. The separate final height-one forest extraction does not justify pruning in higher train coordinates.

**Equal wagon vertex carriers identify wagon labels — reject.** Distinct edge classes can have the same vertex union. Use the checked physical quotient embeddings and their injectivity, never carrier equality alone.

**Ordinary girth is full system girth — reject.** `FullSystemGirthGT` includes linearity and the globally legal supreme-cycle condition; a Berge-girth bound alone does not supply it.

**Arbitrary subfamilies of forests can be handled by unrestricted deletion — reject as a general shortcut.** Use the exact checked deletion/completion lemma with its hypotheses. Do not replace a restricted one-edge deletion statement by arbitrary designated-member heredity.

Historical successor-history/profile/replay explorations should leave the active circulation task list. Preserve genuinely used lemmas and the no-go examples. In particular, do not delete arbitrary long-replacement machinery merely because the current first-stage transfer uses short pieces: the later old supreme plan may contain long pieces.

## 5. Repository and audit infrastructure

At the baseline, the inventory finds **532 proof modules**, **78,354 proof-source lines**, **2,255 lexically recognized named declarations**, **174 Check files**, and **1,635 printed axiom-export occurrences representing 1,633 distinct names**. No executable `sorry`, `sorryAx`, `admit`, custom `axiom`, `unsafe`, `native_decide` or `implemented_by` token was found by the comment/string-aware project-source scan. This is not an exhaustive semantic parser or an independent scan of every external dependency.

There are **77 modules outside the umbrella import closure** and **97 modules with no other proof-module importer**. These sets include legitimate endpoints, regression modules and explicit CI targets. Neither number measures dead code or unfinished proof percentage.

`Girth.RootedForest` was isolated from ordinary proof imports and lacked its own Check file although the coverage document advertised its rooted-path/parent results. Add explicit all-module build coverage and `CheckRootedForest.lean` for its seven exported declarations; do not assert an old build omission merely from umbrella reachability.

The old workflow ran **230 file-level axiom checks for 174 distinct Check files**, including **56 repeated executions**. The replacement discovers every module and every Check file, clears project build objects, builds all modules, and audits each Check file exactly once. It retains the four existing finite regression programs. This removes repeated work without dropping an old audit.

The original axiom-log checker accepted an empty expected declaration set with an empty log as “Checked 0 declarations.” None of the baseline's 174 audit files is empty, so this does not invalidate a past result. Add a fail-closed empty-audit guard and six regression tests. The source scanner has five separate unit tests. All eleven Python tests pass locally; Lean compilation and the repository-wide axiom/regression run remain separate CI gates for the exact final PR head.

The cumulative coverage ledger mixes historical pending notes with newer proved endpoints. Archive it byte-for-byte and replace the active map with explicit checked-interface versus unproved-application columns. No existing proof module is deleted in this audit.

## 6. Revised parallel contracts

**A / #660:** physical minimum-segmentation replacements into a chosen standard, followed by old supremeness and arbitrary-replacement pullback. Never assume the reduced label is an original designated B-label. Separate length-two/order-one retention.

**B / #661:** reuse the actual mixed contained-block obstruction; finish generated output-wagon strongness and linearity without circular use of LinearPretrain.

**C / #662:** instantiate the already checked adjacent-parameter theorem and concentrate new work on filling/subcopy system-girth. Keep cycle-transfer dependencies explicit.

**D / #663:** reuse the actual finite forest increment and well-founded rank; concentrate on forest-to-supreme conversion and recursive witness existence. Do not prune ambient edges in higher coordinates.

The coordinator owns shared interfaces, manuscript markers, imports and CI. The user-requested compact clickable colored margin signs are unchanged. Before a green manuscript marker is added, check the exact statement, hypotheses, actual construction and exact-head axiom audit. No assertion here that the final circulation theorem is complete.
