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


### Boundary reduction batch

[Run 45798581650](https://github.com/janhubicka/lean-girth/actions/runs/45798581650), head 4931c2144f302bc2d25c256746c48e0a855e83fb, again passed all 53 base axiom checks. Every module of the expanded preparation compiled except ContactCopyRestriction, whose two errors concerned a destructured nontriviality witness and identification of generating clique families. The tagged union, strongness, contact traces, G1/G2 preservation, G3 deduction and extracted shortest-cycle window modules all compiled. Their extended axiom audit was skipped; do not claim it passed. Both copy-restriction errors are patched.

New modules:
- ContactCyclicRuns extracts the pure finite run enumeration from the historical library.
- ContactRunSegments constructs the actual closed arcs between successive owner changes, including wrap, with their constituent membership and coverage.
- ContactConstituents identifies core traces and intersections of standard and enlarged-edge constituents.
- ContactBoundary constructs the contracted boundary polygon, proves weight nonincrease, excludes two boundaries, shared chords and any covering clique, from the common-pair consecutive-trace fact.
- ContactSideSubdivision proves the geometric choice of inserted wagon, half-side constituent witnesses, freshness and injectivity of insertions, and noncontainment of the old bad polygon in a standard.
- ContactExpandedPolygon proves the consecutive-trace fact, constructs maximal segments from expanded sides, and derives the positive-core G4 contradiction from an exact finite expansion. The actual cyclic indexing of inserted vertices and its weight equality are the remaining combinatorial obligation of that theorem; they are not assumed solved. The bottom-level forest-core alternative still needs the join-tree bound and special assignment.

Manuscript [1a0ed810d07e9fc0d432eee4cec562e22abe6654](https://github.com/janhubicka/girth/tree/1a0ed810d07e9fc0d432eee4cec562e22abe6654) uses one common-pair consecutive-trace observation instead of the exceptional-triple case distinction for the boundary count, shared chord and covering wagon arguments. This is a mathematical simplification, not a new hypothesis.

One batched CI submission: 53 base, 112 intermediate, 141 extended core audit requests. The intermediate gate prevents a failure in the new finite-cycle arguments from obscuring a successful audit of the picture preparation. The earlier root and main are untouched.


### Actual finite subdivision and positive-core preservation

[Run 45801381497](https://github.com/janhubicka/lean-girth/actions/runs/45801381497), head 10777409c4fe3edadbed4c1b8703503673e6be3e, passed the 53-declaration base gate and the complete 112-declaration picture-geometry and restriction gate. This is the first strict audit of ContactCopyRestriction.preserves_systemGirth, the actual tagged union, strongness, contact trace reflection, G1/G2 and G3 recovery. The expanded gate failed only at ContactRunSegments (two dependent Fin arithmetic normalization goals); subsequent boundary modules were not built. The failures were patched.

ContactExpansionSlots constructs the finite cyclic indexing by keeping every even slot and retaining an odd slot exactly when the side is subdivided. It proves the actual ordered enumeration, its cover, and exact successors including wrap. ContactExpansionConstruction uses the previously drafted insertion-freshness and uniqueness theorems to prove that the new polygon is simple. The weight identity is proved by partitioning the sum over the retained positions into the original slots and selected odd slots. Each split side has weight two in doubled units and is replaced by two sides of weight one. The resulting expand constructor supplies every field of SidePlan.Expansion. ContactPositivePreservation assembles G1–G4 for the actual generated picture at a positive core cut. The only geometric input at that level is the compatible partial gluing on a strongly induced active strip; the application to the ordered train at every level still requires the train adapter. No subdivision or segmentation existence hypothesis is retained in the new positive-core theorem statement.

Independent run-index and subdivision-geometry imports are decoupled so that one CI batch can report their failures in parallel. The next gate requests 157 core audits (161 integration requests). New scripts are NOT certified until a fresh successful build and axiom audit.

Manuscript [695fe33206922b9ec36b206a941f802f3ea18ba4](https://github.com/janhubicka/girth/tree/695fe33206922b9ec36b206a941f802f3ea18ba4) links the verified shortest-wagon-cycle localization and concrete restriction theorem at 10777409. The bridge-pullback, low-order geometry and trace-clique marks explicitly retain the outstanding ordered-strip adapter. Full picture preservation remains marked open.

Next: close all positive-core compilation issues, then derive bottom-level G4 from the selected join-tree property (including the special side assignment and budget); finish mixed forests at level zero, the recursive Ramsey witness and the ordered relational outer theorem. Do not count a passed positive-core theorem alone as full preservation under the two alternatives.


### Bottom-core preservation batch

[Run 45802275426](https://github.com/janhubicka/lean-girth/actions/runs/45802275426), head b04a6fe70b96cfb8c835bd212f071ad47cf8016c, passed the 53- and 112-declaration strict gates again. The extended build also compiled ContactConstituents, ContactCyclicRuns and ContactRunSegments, but failed on local elaboration errors in ContactExpansionSlots, ContactSideSubdivision and ContactBoundary. These reported errors have been patched. The positive-core preservation theorem has not yet been compiled.

New bottom-case proof scripts:
- ContactJoinTree extracts the old verified pure join-tree leaf attachment and deletion lemmas; ContactJoinTreeCycles proves the G4 consequence directly by leaf deletion, even when a contact point is defined by containment of a fixed support in the real-vertex piece. At the bottom cut, a wagon label has the whole edge as its support. This avoids an additional chordal/conformal/Helly adapter in this direction.
- ContactBottomCore derives linearity and G1/G2 from the two-member mixed-forest condition (with the ordinary edge-size and subcopy conditions).
- ContactSegmentBudget charges two weight units to each segment if no segment is one mixed side; ContactBottomBoundary constructs the actual set of used labels and applies its selected join tree.
- ContactBottomOwners proves that a mixed side between core points is a physical vertex--edge incidence under the one-edge absorption property. It gives that side the owner of the other side at its wagon endpoint, with no conflict by badness. No side-assignment existence hypothesis remains.
- ContactBottomPreservation assembles G1--G4 using this special assignment and the selected join trees, without assuming G3/G4 of the bottom core. Explicit inputs include the one-edge trace property (BottomAbsorption), a strongly induced core, singleton output wagons, and the mixed-forest hypotheses on the core. The ordered-strip adapter for those inputs remains open.

Manuscript [43987464d0ba3e3bf86e5ff41f2c29a3b5d23516](https://github.com/janhubicka/girth/tree/43987464d0ba3e3bf86e5ff41f2c29a3b5d23516) simplifies the special bottom side assignment: any constituent containing the singleton wagon contains its full edge. Assigning its mixed core side to the constituent of the other side is valid, and cannot conflict with another such assignment. This replaces the unnecessary private-endpoint case discussion.

One CI-triggering commit submits 180 core audit requests (184 integration), with the 53 and 112 strict intermediate gates retained. The new bottom proofs and the corrected positive-core scripts await successful compilation and axiom checks. Still open: bottom system-girth to complete mixed forests (particularly conformality and the converse join-tree construction), ordered/all-level adapters, and recursive/outer witness assembly. No new manuscript green marks from the uncertified extension.


### Converse forest obstruction and boundary certification batch

[Run 45804788818](https://github.com/janhubicka/lean-girth/actions/runs/45804788818), head 1668a6f148fd738596f6829573e4c0e36f56b143, again passed the 53 and 112 strict audit gates. The expanded build successfully compiled ContactConstituents, ContactJoinTree, ContactExpansionSlots, ContactCyclicRuns, ContactSideSubdivision, ContactRunSegments, ContactSegmentBudget and ContactBoundary. Thus the finite doubled-slot enumeration, fresh subdivision choices, closed cyclic segments and entire boundary contradiction are compiled. Two remaining failures were a mixed existential-binder syntax error in the Expansion record and a subtype nonmembership simplification in ContactJoinTreeCycles. Both have been corrected; the dependent assembly modules have not yet been compiled, and the extended audit was skipped.

New proof scripts:
- ContactSelectedCycles rules out every bad polygon of real vertices of a selected family of at most q pieces. The side owners are injective, so the length budget is a consequence rather than a premise.
- ContactConformality excludes minimal uncovered cliques. A triangle reduces to the previous bad-polygon lemma, and four distinct one-point deletion witnesses give three distinct actual ambient edges forming a labelled Berge triangle. The general finite clique uses a minimal counterexample and an injection of its deletion witnesses into the selected family.
- ContactJoinTreeGlue extracts the pure binary bridge and reindexing constructions, and ContactJoinTreeRestore constructs join trees when restoring a private vertex or a leaf (including a contained carrier). These are useful constructive tools, not a proof of the remaining chordal/conformal-to-join-tree implication. That implication and the full mixed-forest converse remain open.

Manuscript [c4543d869ba601a22cbcf36ca87d6923299d84d3](https://github.com/janhubicka/girth/tree/c4543d869ba601a22cbcf36ca87d6923299d84d3) unifies the uncovered triangle and longer chordless cycle proofs, explicitly proves distinctness of the three common edges in the larger-clique case, and marks only the already audited pairwise and sparse-polygon kernels as verified.

This batch adds a separate 153-declaration boundary base gate, so the already compiled independent geometry is axiom-audited before the new assembly. The expanded core requests 193 audits (197 integration). One non-skipped commit submits all changes. No full preservation theorem, complete mixed-forest converse, ordered train adapter, or recursive Ramsey witness is certified yet.


### Complete join-tree converse batch

[Run 45806522232](https://github.com/janhubicka/lean-girth/actions/runs/45806522232), exact head 1f184f09645b84aed09f7155d7719e80d6416bb1, passed all three intermediate gates (53, 112, and 153 audited declarations; standard logical axioms only). This certifies the full abstract boundary contradiction, actual cyclic-run segmentation, geometric subdivision choices and the doubled-slot indexing, as well as the segment budget. The expanded build also compiled ContactSelectedCycles, ContactJoinTreeCycles, ContactJoinTreeGlue and ContactJoinTreeRestore. The remaining errors in ContactExpandedPolygon (section-variable inclusion), ContactBottomCore (explicit carrier coercion) and ContactConformality (two finite-set membership goals) were patched. The full positive and bottom preservation assembly remains uncertified.

The new generic graph-theory proof scripts are:
- ContactChordalPaths constructs induced paths from shortest walks and excludes separated pairs of induced paths in a chordal graph.
- ContactMinimalSeparator constructs minimum-cardinality vertex separators and proves that each is a clique using the two full components.
- ContactSimplicial proves the strong simplicial-vertex lemma outside any proper clique by induction on a component together with its separator.
- ContactJoinTreeConverse constructs actual join trees by induction on the number of labelled pieces plus used vertices. Remove a contained piece; otherwise conformality and a simplicial used vertex give a private vertex. Restore the tree using the earlier construction.
- ContactJoinTreeCharacterization supplies both directions of the finite running-intersection tree theorem.
- ContactMixedForestConverse assembles the whole level-zero conclusion from the actual selected-family obstructions and the independently constructed join-tree theorem.
These are complete proof scripts without an assumed simplicial-vertex, chordal/conformal converse, or join-tree existence axiom, but have not yet passed Lean compilation. The shared mixed-forest definitions now reside in ContactZeroJoinTrees.

Manuscript [7bab56e5c97da9929c1dbae97de2bc46b13eadc3](https://github.com/janhubicka/girth/tree/7bab56e5c97da9929c1dbae97de2bc46b13eadc3) includes immutable links to the certified 153-declaration boundary gate and explicitly retains the remaining assembly and ordered-adapter obligations. The shared-chord argument now explicitly distinguishes the copy-copy case from a chord belonging to a wagon clique.

One CI-triggering commit submits 216 core audit requests (220 integration) and retains the 53, 112, 153 intermediate gates. The main open tasks remain kernel certification of the preservation and mixed-forest assembly, the ordered/all-level train adapters, forest increment/completion and the actual recursive/outer Ramsey witnesses.
