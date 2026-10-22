import Girth.TrainCyclicRestrictionRegression

/-!
# Axiom audit for the manuscript's typed cyclic-restriction component

The workflow must compile the two imported modules before reading this
output.  These checks cover every public proof/constructor export of
TrainCyclicRestriction, including the finite-position and numerical core,
and the three named concrete regression proofs.

The acceptable-cycle export keeps the separate order-one designation
hypothesis.  None of these exports claims that the geometric restriction
hypotheses have already been instantiated for the full amalgamation reduct.
-/

-- Cyclic restriction of actual finite position sets, including wrap.
#print axioms StructuralRamsey.Girth.CyclicRestriction.successor_of_source_successor
#print axioms StructuralRamsey.Girth.CyclicRestriction.predecessor_of_source_predecessor
#print axioms StructuralRamsey.Girth.CyclicRestriction.successor_across_deleted_position
#print axioms StructuralRamsey.Girth.CyclicRestriction.restrict_consecutive_window
#print axioms StructuralRamsey.Girth.CyclicRestriction.restrict_deleted_neighbour_window

-- Direct order bound, without an assumed partition into runs.
#print axioms StructuralRamsey.Girth.CyclicRestriction.twiceWeight_restrict_le

-- Actual typed BigCycle constructor and the geometric input structure.
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.restrictConnectorWord
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.mk

-- Every public transfer theorem in RestrictionMap.
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.length_le
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.twiceOrder_le
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.source_vertex
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.source_wagon
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.contact_source
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.A2_positions
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.A2
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.source_wagon_deleted
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.A3
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.acceptable
#print axioms StructuralRamsey.Girth.OrderOneData.BigCycle.RestrictionMap.restrict

-- Named regression proofs: source, deleted-wagon wrap, retained-wagon sides.
#print axioms StructuralRamsey.Girth.OrderOneData.CyclicRestrictionRegression.source_acceptable
#print axioms StructuralRamsey.Girth.OrderOneData.CyclicRestrictionRegression.vertices_acceptable
#print axioms StructuralRamsey.Girth.OrderOneData.CyclicRestrictionRegression.wagonAndSides_acceptable
