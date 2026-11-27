import Girth.ContactValidation

-- Recursive construction and the partite lemma.
#print axioms StructuralRamsey.Girth.contactProfileRamsey_wellFounded
#print axioms StructuralRamsey.Girth.contactProfileRamsey_distinctImages
#print axioms StructuralRamsey.Girth.contactProfileForestRamsey
#print axioms StructuralRamsey.Girth.contactLocalForestPartite

-- Outer construction and the quantitative completion bound.
#print axioms StructuralRamsey.Girth.contact_minimumCompletion_cost
#print axioms StructuralRamsey.Girth.contactOrderedOuterRamsey_qualitative
#print axioms StructuralRamsey.Girth.contactOrderedOuterRamsey_quantitative
#print axioms StructuralRamsey.Girth.contactRelationalSupportWitness_exists
#print axioms StructuralRamsey.Girth.contactRealizeSupport

-- The actual main theorem, first on embeddings and then on literal copy carriers.
#print axioms StructuralRamsey.Girth.ContactActualMixedCompletion
#print axioms StructuralRamsey.Girth.ContactCarrierMixedCompletion
#print axioms StructuralRamsey.Girth.contactRelationalGirthRamsey
#print axioms StructuralRamsey.Girth.contactRelationalGirthRamsey_carriers

-- The unordered hypergraph theorem, including all-edge colouring and the budget.
#print axioms StructuralRamsey.Girth.ContactUniformLocalCompletion
#print axioms StructuralRamsey.Girth.ContactUniformRamseyWitness
#print axioms StructuralRamsey.Girth.contactUniformLocalRamsey

-- Completing the order under the stated non-order irreducibility hypotheses.
#print axioms StructuralRamsey.Girth.contactCompleteOrder_equiv
#print axioms StructuralRamsey.Girth.contactCompleteOrder_girth_arrow
#print axioms StructuralRamsey.Girth.contactCompleteOrder_fullCorollary

-- Exact vertex bound in the small induced relational consequence.
#print axioms StructuralRamsey.Girth.contactComparisonGraph
#print axioms StructuralRamsey.Girth.contact_small_comparison_chordal
#print axioms StructuralRamsey.Girth.contact_small_induced_supported
#print axioms StructuralRamsey.Girth.ASupportedTreeAmalgam.comparison_chordal
#print axioms StructuralRamsey.Girth.contactComparisonGraph_chordal_of_supportedTree_embedding

-- Forgetting order preserves the actual supported-tree recursion.
#print axioms StructuralRamsey.Girth.ASupportedTreeAmalgam.contact_orderReduct
#print axioms StructuralRamsey.Girth.contact_uniform_induced_reduct
#print axioms StructuralRamsey.Girth.ContactUniformSmallRamseyWitness
#print axioms StructuralRamsey.Girth.contactUniformSmallRamsey_edgeless
#print axioms StructuralRamsey.Girth.contactUniformSmallRamsey

-- The arbitrary-size chordality criterion, using actual maximal-clique bags
-- and an induced embedding into a supported tree obtained by unfolding.
#print axioms StructuralRamsey.Girth.contact_chordal_copyWitness
#print axioms StructuralRamsey.Girth.contact_trace_tree_embeds_supported
#print axioms StructuralRamsey.Girth.contact_induced_supported_of_chordal
#print axioms StructuralRamsey.Girth.contact_induced_supported_iff_chordal

-- Finer-cut localization and the parent-by-parent wagon-girth formulation.
#print axioms StructuralRamsey.Girth.ContactHypergraphData.finer_cycle_in_one_coarser_wagon
#print axioms StructuralRamsey.Girth.ContactHypergraphData.finer_cycle_in_one_coarser_wagon_of_acyclic
#print axioms StructuralRamsey.Girth.ContactHypergraphData.properWagonGirth_iff_parentWagonGirth

-- General incidence-forest traces and auxiliary-node erasure.
#print axioms StructuralRamsey.Girth.contact_labelledGirth_of_incidence_acyclic
#print axioms StructuralRamsey.Girth.contact_trace_joinTree_of_incidence_acyclic
#print axioms StructuralRamsey.Girth.ContactJoinTree.erase_of_incidence_acyclic

-- Covered ordered linear seeds and the strongness of complete wagons.
#print axioms StructuralRamsey.Girth.contactCoveredLinearSeed
#print axioms StructuralRamsey.Girth.OrderOneData.contact_wagon_strong
#print axioms StructuralRamsey.Girth.OrderOneData.contact_outside_wagon_intersection_subsingleton

-- The triangulation observation for arbitrary metric weights.
#print axioms StructuralRamsey.Girth.ContactCoveredTriangulation.triangleCount_add_two
#print axioms StructuralRamsey.Girth.contactCoveredTriangulation_of_metricG4
#print axioms StructuralRamsey.Girth.contactCoveredSide_of_metricG4
#print axioms StructuralRamsey.Girth.contactSharedChordBound_of_metricG4
#print axioms StructuralRamsey.Girth.contactSharedChordBound_iff_metricG4

-- Full parent-first and admissible-enumeration statements.
#print axioms StructuralRamsey.Girth.ContactJoinTree.parentFirst_inter_eq
#print axioms StructuralRamsey.Girth.contact_joinTree_of_admissibleRank
#print axioms StructuralRamsey.Girth.contact_admissibleRank_of_attachments
#print axioms StructuralRamsey.Girth.contact_joinTree_of_admissibleAttachments
#print axioms StructuralRamsey.Girth.ContactJoinTree.parentFirstRank_admissible
#print axioms StructuralRamsey.Girth.ContactJoinTree.exists_admissibleRank_leaf_last
#print axioms StructuralRamsey.Girth.contact_joinTree_iff_admissibleRank

-- Exact completion-budget sharpness on actual ordered edge-copy unions.
#print axioms StructuralRamsey.Girth.contactSharp_actual_completion
#print axioms StructuralRamsey.Girth.contactSharpCycle_mixedUnion_no_embedding
#print axioms StructuralRamsey.Girth.contactSharpCycleStar_union_iso
#print axioms StructuralRamsey.Girth.contact_vertex_cutoff_cycle_obstruction

-- The full witness showing the exact small-vertex cutoff is sharp.
#print axioms StructuralRamsey.Girth.contactSharpTwoPoint_input
#print axioms StructuralRamsey.Girth.contactSharpPureCycle_completion
#print axioms StructuralRamsey.Girth.contact_vertex_cutoff_sharp
