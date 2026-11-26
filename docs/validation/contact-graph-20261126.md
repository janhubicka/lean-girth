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


## Progress during the second validation pass

- Exact head 919614660b7ee6f05c696087acc92dfe774949ee: [Actions run 45793846599](https://github.com/janhubicka/lean-girth/actions/runs/45793846599) passed the standalone build and all 34 printed axiom checks (the job was cancelled only in post-build caching). This includes ContactSubstitution.preserves_systemGirth for its explicit covering record, all mixed triangle/quad lemmas, and the new half-cutoff rank. The integration gate was not run.
- The reusable cyclic restriction weight inequality was extracted from the older TrainCyclicRestriction proof. ContactPolygonSplit constructs the two chord arcs as order embeddings; ContactCoveredSide implements the side-triangle clause. These new proofs require a fresh passing exact-head gate; the first split run failed on two Fin arithmetic normalization steps, subsequently patched.
- ContactCoreGeometry and ContactAttachmentGeometry implement the common-wagon, mixed triangle and global wagon-linearity arguments with an explicit free-union interface. The actual picture adapter, including incidence pullback and local wagon comparison, remains a genuine obligation. Do not mark the manuscript theorem verified on the basis of an interface theorem.
- Heuristic progress across the full new manuscript including reusable infrastructure: approximately 30–35%, weighted by difficulty rather than source lines. The entire new proof, in particular the G4 picture preservation and recursive witness, is not yet certified.


## Batched validation pass (26 November)

The manuscript has a new reviewed baseline [girth@e9ce630dea068f37d3a682ec42489830b2494949](https://github.com/janhubicka/girth/tree/e9ce630dea068f37d3a682ec42489830b2494949): new figures, duplicate obsolete proof removed, unified two-point incidence proof, and copy restriction localized to an old clique with omitted vertices simplicial within a component. The substantive statements remain unchanged.

- [Run 45794906628](https://github.com/janhubicka/lean-girth/actions/runs/45794906628) compiled ContactPolygonSplit, ContactCoveredSide and ContactCoreGeometry, but failed on the final symmetry elaboration in ContactAttachmentGeometry. That failure is corrected; the enlarged base axiom gate still requires an exact-head pass.
- ContactPictureData derives all ContactAttachmentGeometry fields from exact common-core vertex, edge and wagon embeddings and coverage, including the bridge pullback and local pair comparison. Constructing these maps from the ordered train picture remains an adapter obligation.
- ContactBadCycle and ContactCliqueRestriction implement shared-chord localization, absence of three points of a bad polygon in one clique, and abstract G4 restriction.
- ContactCopyRestriction proves G1–G4 for concrete component/selected-edge data, rather than assuming a graph restriction theorem as a premise.
- ContactLevelZero gives the pairwise allowed intersection and short polygon-to-labelled-Berge-cycle arguments. The complete join-tree equivalence and conformality adapter remain open.
- One non-skipped push submits this batch. The workflow now first checks ContactBase (53 declarations), then the enlarged ContactCore (79 declarations), retaining only standard logical axioms. The cache key is pinned by toolchain and manifest, not source SHA; dependencies are saved before proof checking, with project build objects removed. This avoids downloading the same dependency cache repeatedly on proof failures.

All new results in this batch await compilation/axiom checks. Do not mark the manuscript green based on drafted code or the earlier partial compile.


### Checked base and second batched submission

The base step of [run 45796794888](https://github.com/janhubicka/lean-girth/actions/runs/45796794888), exact head 48ef9d05bc86bb62d2dede343dd9345f95f6c735, succeeded: 53 declarations use only standard logical axioms, including the actual chord split, both short-cycle conclusions, and the interface theorem on attachment wagon linearity. ContactBadCycle also compiled, but was not yet covered by the completed axiom gate. The extended step failed in three adapter modules on elaboration issues; no new extended certification is claimed. The dependency cache save succeeded. That run measured 25 fast and 56 integration modules out of 1010 project modules.

The next batch fixes the reported errors and adds ContactTaggedPicture, which explicitly constructs generated vertex, edge and wagon labels from compatible partial injections. The geometric input consists of exact gluing-domain, edge-carrier and parent compatibility; the adapter from the ordered active strip remains to be shown. The core gate now requests 87 audits. Only this final commit triggers the follow-up CI.

Manuscript revision [f17051524f2737757505c16d8c5f59eb13710da3](https://github.com/janhubicka/girth/tree/f17051524f2737757505c16d8c5f59eb13710da3) includes the new exceptional wagon-triple observation in the preservation argument and immutable validation links for the two-sort short-cycle observation and substitution. The general arbitrary-metric observation and the actual picture-step theorem are not marked fully verified.


### Preservation-focused batch

[Run 45797414545](https://github.com/janhubicka/lean-girth/actions/runs/45797414545), exact head c72da19cdfdc7de7f5d7bb02a8220a598a060954, reconfirmed the 53 base axiom audits. ContactPictureData, ContactBadCycle and ContactLevelZero compiled. The extended step failed on two definitional equalities in the tagged parent surjectivity proof and an unspecified predicate in the cyclic component propagation proof. These have been patched; the complete 87-declaration gate did not pass and no new axiom certification is asserted for those three compiled modules.

The next batch extracts the pure shortest labelled Berge-cycle geometry from TrainSystemCut* at 99d26270 (ContactBergeWindows). ContactWagonGirth proves localization and the deduction of G3 from G4 and local G3. ContactPictureStrong derives actual core and standard strongness and edge linearity from the strong active strip. ContactPictureCliques gives the entire generating-clique trace lemma and both directions of adjacency. ContactPictureInvariant implements G1/G2 preservation, the bottom two-point alternative, and contraction of a locally supported labelled Berge cycle. These are new scripts awaiting the kernel and axiom gate (112 core / 116 integration requests).

The manuscript at [d722de9a2d5be7aae2b6e64b987e83c64989364a](https://github.com/janhubicka/girth/tree/d722de9a2d5be7aae2b6e64b987e83c64989364a) now separates shortest-wagon-cycle localization and simplifies the final boundary lifting. It is unnecessary to eliminate subdivisions before lifting: a segment with endpoints shared by the covering standard and another constituent cannot span the outer points of an exceptional wagon triple, so it is a single side of the subdivided polygon. This avoids the former additional argument about inserted wagon vertices.

Remaining central obligation: construct the subdivided polygon and cyclic segment boundaries and prove G4, with separate level-zero forest completion for the core. The ordered partite train interfaces and complete recursive witnesses are still open. New proof scripts are not counted as verified until the exact-head audit. The current batch is submitted with one non-skipped commit; historical code and main remain intact.
