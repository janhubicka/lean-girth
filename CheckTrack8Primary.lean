import Girth.FiniteTracePEOCount
import Girth.FiniteTraceSuccessorCycle
import Girth.FiniteTraceSimplicialCriterion

/-!
# Focused Track 8 kernel gate — direct PEO-counting route

The small-trace proof NO LONGER requires constructing a clique tree,
parent forest, or deleting contained bags.  This gate imports only the
direct trace-count route and the cyclic-pair obstruction.

Exact remaining mathematical input: a finite chordal trace pair
graph admits a perfect elimination order.  In particular, no lemma
below claims this unformalized graph theorem.

Run with the repository-pinned Lean/Mathlib toolchain. Do not promote
manuscript validation markers without actual compilation AND executed
#print axioms, checking transitive dependencies and assumptions.
-/

#check StructuralRamsey.Girth.JoinTree.pairCovered_in_one_bag
#check StructuralRamsey.Girth.exists_original_bag_covering_faces_of_card_ge_three
#check StructuralRamsey.Girth.traceConformal_of_local_completion
#check StructuralRamsey.Girth.JoinTree.no_cyclic_unique_pairs
#check StructuralRamsey.Girth.no_bounded_chordless_pair_pattern
#check StructuralRamsey.Girth.no_bounded_chordless_successor_cycle
#check StructuralRamsey.Girth.maximalClique_eq_laterNeighborBag
#check StructuralRamsey.Girth.maximalTraceRepresentatives_cover
#check StructuralRamsey.Girth.maximalTrace_eq_eliminationBag
#check StructuralRamsey.Girth.maximalTrace_card_le_of_PEO
#check StructuralRamsey.Girth.smallTrace_selection_of_PEO
#check StructuralRamsey.Girth.smallTrace_selection_of_local_completions_and_PEO

#print axioms StructuralRamsey.Girth.JoinTree.pairCovered_in_one_bag
#print axioms StructuralRamsey.Girth.exists_original_bag_covering_faces_of_card_ge_three
#print axioms StructuralRamsey.Girth.traceConformal_of_local_completion
#print axioms StructuralRamsey.Girth.JoinTree.no_cyclic_unique_pairs
#print axioms StructuralRamsey.Girth.no_bounded_chordless_pair_pattern
#print axioms StructuralRamsey.Girth.no_bounded_chordless_successor_cycle
#print axioms StructuralRamsey.Girth.maximalClique_eq_laterNeighborBag
#print axioms StructuralRamsey.Girth.maximalTraceRepresentatives_cover
#print axioms StructuralRamsey.Girth.maximalTrace_eq_eliminationBag
#print axioms StructuralRamsey.Girth.maximalTrace_card_le_of_PEO
#print axioms StructuralRamsey.Girth.smallTrace_selection_of_PEO
#print axioms StructuralRamsey.Girth.smallTrace_selection_of_local_completions_and_PEO

#check StructuralRamsey.Girth.IsSimplicialWithin
#check StructuralRamsey.Girth.IsSimplicialWithin.mono
#check StructuralRamsey.Girth.isSimplicialWithin_iff_clique
#check StructuralRamsey.Girth.isPerfectEliminationOrder_iff_simplicialSuffix
#check StructuralRamsey.Girth.isSimplicialWithin_of_clique
#check StructuralRamsey.Girth.exists_simplicialOutside_clique
#check StructuralRamsey.Girth.isSimplicialWithin_univ_of_neighbors_subset

#print axioms StructuralRamsey.Girth.IsSimplicialWithin.mono
#print axioms StructuralRamsey.Girth.isSimplicialWithin_iff_clique
#print axioms StructuralRamsey.Girth.isPerfectEliminationOrder_iff_simplicialSuffix
#print axioms StructuralRamsey.Girth.isSimplicialWithin_of_clique
#print axioms StructuralRamsey.Girth.exists_simplicialOutside_clique
#print axioms StructuralRamsey.Girth.isSimplicialWithin_univ_of_neighbors_subset
