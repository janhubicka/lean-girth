# Main-draft formalization coverage

Source manuscript: `janhubicka/girth`, current `main.tex` entry point.

| Manuscript item | Lean status |
| --- | --- |
| §1 embeddings / image copies | represented by `RelStructure.Embedding` and `Girth.copyCarrier` |
| §1 support hypergraph | `Girth.supportCopies` |
| §1 A-linear support | `Girth.ALinear` |
| §1 A-strongly induced | `Girth.AStrong` |
| §1 Berge cycle / girth (>g) | `Girth.BergeCycle`, `Girth.GirthGT` |
| girth (>2) implies linear support | proved by `pairwise_subsingleton_of_girthGT_two`, `aLinear_of_girthGT_two` |
| subhypergraphs preserve a girth lower bound | proved by `girthGT_of_subset` |
| adding one fresh edge preserves Berge girth | exact old-short-path equivalence `girthGT_insert_iff_no_shortBergePath` in `BoundaryGirthExtension`; both directions proved, including length-two cycles |
| finite marked boundary record for girth | `hasShortBergePathToEdge_iff_marked`, `freshEdge_girth_iff_of_sameShortPaths`, `freshEdge_girth_iff_of_equalShortPathRecords`, `markedShortPathRecord_mono`, `markedShortPathChanges_bound`; these assume all attachment contacts are marked and an increasing old edge process for event bounds |
| finite marked B-carrier contact certificates | `markedCarrierRepresentatives_card_le`, `markedCarrierRepresentatives_cover`, and `freshCarrier_allContacts_iff_representatives` reduce all one-new-carrier intersection tests to finitely many old carriers, assuming every old contact lies on marked vertices; they do **not** produce an outer join tree or bound histories |
| one dominated forest-leaf attachment | `freshCarrier_dominated_iff_representatives` and `forestOfCopies_attach_dominated_of_marked_contacts`: finite marked carrier masks decide whether an old member dominates every overlap; combined with `forestOfCopies_attach_dominated` this proves a genuine join-tree extension, conditional on marked contact and allowed intersections. General multiple-owner joins and successor-history lifting remain open. |
| coherent owner-labelled girth certificate | `coherentCycleOwnerCore_subset`, `coherentCycleOwnerCore_covers`, `coherentCycleOwnerCore_mono`, `coherentCycleOwnerCore_card_le`, and `coherentCycleOwnerSupport_girth_iff`: retain the *whole* designated B-piece first owning each selected support-edge witness, at most `g * 2^|K|` old B-owners, preserving girth for all subsets of the candidate batch at all stages under monotone support/owner coverage and ambient edge containment; the retained owners do not automatically form a forest or a legal free-successor history. |
| §1 A-supported tree amalgam | `Girth.ASupportedTreeAmalgam` |
| A-supported ⇒ generic tree amalgam | proved by `ASupportedTreeAmalgam.toTreeAmalgam` |
| irreducibles / A-copies in supported trees lie in constituent B-copies | proved by `irreducible_contained_in_copy`, `aCopy_contained_in_copy` |
| finite copy containment forces equal carriers | proved by `sameCopy_of_range_subset`; supported-tree specialization `bCopy_same_constituent` |
| A-copy coverage in supported trees | proved by `ASupportedTreeAmalgam.aCopiesCoveredByB` |
| A-linearity + controlled B-intersections imply B-copies are A-strong | proved by `aStrong_of_linear_and_controlled` |
| supported-tree B-copy intersections are controlled | proved by `ASupportedTreeAmalgam.bIntersectionsControlled` |
| singleton B-copy intersections are A-supported on both sides | proved by `ASupportedTreeAmalgam.singletonIntersectionsSupported` |
| §2 EHN / partite structural input | merged functional EHN imported from `partite-construction`; `FreeAmalgamationClass.orderedRamsey_of_mem_target` now instantiated for the girth closure class |
| Ramsey + generic bounded local-tree + irreducible coverage core | `localTreeRamseyCore` |
| Lemma 2.1 geometry of A-supported tree amalgams | fully proved; `ASupportedTreeAmalgam.girthGT`, `bIntersectionsControlled`, `singletonIntersectionsSupported`, `aLinear_of_base_and_controlled`, `aStrong_of_linear_and_controlled` |
| Observation 2.2 closure expansions | actual c_A expansion, `IsClosed ↔ AStrong`, hereditary closed substructures, and class-level full free amalgamation from arbitrary full embeddings now encoded through CI |
| Theorem 2.4 A-linear Ramsey theorem | full functional-EHN derivation encoded in `ALinearRamsey`; ordered specialization and Ramsey-family geometry now through CI |
| §4 forest of copies / join trees | definitions, running intersections, leaf-attachment equality, canonical rooted paths/parents, and singleton-attachment girth induction formalized; `exists_dominating_member_of_comparable` and `exists_incomparable_intersections_of_not_forest` now need only finitely many pieces, not a finite ambient vertex set |
| Structural local-forest translation | transversal decoration, exact support, and irreducible containment encoded in `Decoration`/`HypergraphClique`; lifting strong partite embeddings remains |
| §5 initial/active picture | designated initial components and irreducible coverage formalized; true active subsystem, custom local witness, projection/actual irreducible coverage, Ramsey picture property, standard-copy geometry, designated B-copy preservation, active-subsystem A-generation, shared-support core mechanism, and the bridge from strong local-forest support families to the designated local hypothesis now encoded through CI |
| §5 untouched-subsystem girth | The conditional picture-step contradiction `no_short_untouched_projected_cycle` is formalized, using `projectedCopy_subset_standardActive`, `no_short_support_cycle_of_owner_mapped_forest`, and `RawCyclicIncidenceData.exists_compressed_le`. The structural local-forest input still needs assembly at the manuscript's quantifier level. |
| §5 local forest geometry | `StrongSupportEmbedding.supportPiece`, `localForestSupportPiece_carrier_eq_copy`, and `strongSupportPieces_meetPartAtMostOne` relate the local witness's support pieces to decorated standard copies and fine parts. |
| §5 forest completion assembly | `ownerFiber_card_add_degree_le`, `forestOfCopies_lift_local_of_linear`, `ForestOfCopies.restrict_compl_of_oneEdge`, `ForestOfCopies.restrict_mixed_of_auxiliary_A`, and `forestCompletion_assemble` prove the counting, join-tree gluing, and removal of all auxiliary one-edge members. Actual designated local completion witnesses and their incorporation in the full picture invariant remain to be supplied. |
| §§3–6 global iteration | The existing `activePictureStep_invariants` checks projection, irreducible coverage, Ramsey property, and intersections. The full `certpres` implication, including local forest witnesses and the completion quantifiers, is not yet a Lean theorem. |
| Main Theorem 1.1 | not yet formalized end-to-end |

The dependency on `partite-construction` is pinned deliberately.  As the EHN
and recursive/iterated construction formalization there advances, this project
can bump the pin and replace assumptions or wrappers by stronger checked
interfaces.
