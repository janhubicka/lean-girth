# Validation plan: weighted contact-graph manuscript (26 November 2026)

Exact manuscript: [girth@4d92811d2f2e17e87611cd12288e9e20163acfda](https://github.com/janhubicka/girth/tree/4d92811d2f2e17e87611cd12288e9e20163acfda), entry point regular-tree-girth.tex.
Historical Lean baseline: lean-girth@99d26270dea77a88527d83ee93f7d576f316d9b4. Lean v4.35.0-rc3 and the existing pinned dependency manifest are unchanged.

This branch is an independent validation programme, NOT a new certification of the old proof. No old cycle-system theorem implies the weighted contact-graph definition without an explicit proof. Keep the old main and PRs intact.

## Reuse inventory

| Manuscript obligation | Existing reusable source | Remaining work |
| --- | --- | --- |
| Relational A-support, rigidity, linearity | Support, Berge, SupportedTree, RelationalUnionFreeAmalgam, MixedForestInduction; partite-construction | Check the new hypergraph reduction, exact labelled seed, and restoration of one-point types; actual selected witness |
| Indexed Berge cycles and wagon girth | LabelledWagonCutRestriction (now pure LabelledBergeCore), TrainWagonClassRestriction, TrainLabelledCutGirth, TrainCutGirthProjection | Exact indexed parent-by-parent adapter; not merely set-range girth |
| Forest definition and join-tree assembly | Forest, ForestEnumeration, ForestTreeRewire, ForestJoinGlue, ForestAuxiliaryDeletion, ForestCompletionAssembly, ForestCompletionProperty, ForestCompletionChoices | General node erasure with acyclic edge separators, not just one-edge/singleton deletion; chordal/conformal equivalence; actual mixed increment |
| Marked support in outer construction | ForestGirth, ForestIncidenceAcyclic, previous direct increment/owner geometry | Recheck exact one-marked-edge-per-member and selection arguments |
| Exact gluing of wagon trees | TrainWagonNodeGluing, TrainWagonGeneratedKernel, TrainPhysicalPictureGeneratedTrain, TrainGeneratedActualAllLevelRestriction, TrainCoreWagonEmbedding, TrainCoreWagonBridge | Build adapters to actual indexed hypergraph picture; don't import all old relational geometry merely for a simple quotient lemma |
| Contact graph weights and G1/G2 | TrainCycleWeights and the carrier record OrderOneData (moved to TrainIncidenceData) | New ContactGraph definitions and local lemmas |
| Chordal G4 and shared chords | No direct historical equivalence; old supreme-cycle statements are not replacements | ContactCycles: reverse direction, forward induction conditional on explicit polygon cuts; construct both cyclic interval maps and weight bounds; covered-side clause |
| Two-point wagon incidence/linearity | Intrinsic old wagon linearity and exact core restriction | ContactLowOrder mixed triangles/quadrilateral; bridge pullback, two-point lemma and actual output linearity still need adapters |
| Substitution | TrainFillingTemplateConstruction, TrainFillingInheritedTrain, TrainFillingInheritedParameters | ContactSubstitution proves all clauses under concrete covering/label data; construct those data from ordered filling. Extract the reusable construction rather than importing TrainFillingSystemGirth |
| Copy restriction | Old TrainDesignatedSubcopyStrong, TrainDesignatedSubcopyGirth | New shared-chord proof; parent-component carriers, retained intersection and contact edges |
| Single-part refinement | TrainRecursiveRefinementGirthGain, TrainCutGirthProjection, RefinementRunCount | New 2g+1 bound needs geometric run projection, including repeated child labels; ContactRank contains arithmetic |
| Recursion termination | TrainCutoffLexRank, TrainCutoffWellFounded | ContactRank adapts exactly to max(2,q/2), arbitrary inserted depth |
| Train Ramsey induction | Old indexed witness and backward-selection machinery | New forest boost, filling at cutoff two, preserved G1–G4; no old full-system oracle |
| Main outer theorem and quantitative cost | MixedForestInduction, CompletionBudget, old selected-copy gluing | Exact outer forest-extension witness, degree/erasure argument, induced order restoration, final theorem |

## Deliberately excluded old machinery

Acceptable/normal cycle syntax, simultaneous supreme plans, long/short replacement words, freshness conditions, reductions and lifted cycle words are not active validation targets. Some old files contain useful carrier maps adjacent to obsolete cycle proofs. Extract those maps and their exact hypotheses when needed rather than reintroducing the old dependency closure. Likewise the experimental diary/port/replay branches are not part of the new proof.

## Build policy

Fast gate: lake build +Girth.ContactCore, then lake env lean CheckContactCore.lean, then scripts/check_axioms.py on exactly the printed declarations. The inventory script rejects relational/obsolete cycle dependencies in the fast core. It compiles the new core from this checkout; no stale project olean is accepted as a new certificate.

Integration gate: lake build +Girth and CheckContactGraph.lean; run with workflow_dispatch integration=true when the adapter/outer proof is being validated. It is required before considering a merge. The original hundreds of historical source and Check files remain available but are excluded from active builds, so no proof is lost. No physical mass deletion until the new dependency graph and final proof are certified.

The initial declarations in ContactGraph, ContactSubstitution, ContactCycles, ContactLowOrder and ContactRank are proof scripts awaiting exact-head kernel/axiom results. In particular, the polygon-split premise in contactSharedChordBound_of_G4_of_splits is a real outstanding obligation. A successful axiom audit of this conditional lemma does not establish G4 implies the shared-chord bound. The ordered substitution theorem likewise requires constructing the actual covering record. Do not update manuscript green markers on the strength of conditional or merely drafted code.

## Next order of work

1. Compile and strictly check the standalone core, fix elaboration problems before adding more dependencies.
2. Finish cyclic-interval split and covered-side extraction. Build low-order attachment geometry from the actual gluing maps.
3. Prove restriction and full preservation, both core alternatives, and level-zero mixed forests.
4. Port forest boost, cutoff-two ordered filling and single-part refinement; close the true rank-recursive witness.
5. Audit the arbitrary-B outer construction and quantitative completion; run a clean full integration check. Keep the draft PR unmerged until the new theorem is genuinely validated.
