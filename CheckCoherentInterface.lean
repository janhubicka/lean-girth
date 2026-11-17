import Girth.CoherentSharedOccurrence
import Girth.CrossPortP4Endpoint
import Girth.SupportedPartialClosureEquiv

/-!
# Focused axiom audit for the new coherent-port research modules

This is intentionally separate from the circulation theorem's pinned
certification. The project's full Lean workflow builds every Girth module
and runs its standard strict #print axioms parser on every Check*.lean.
No trusted extra axiom, sorry or placeholder is permitted.
-/

#print axioms StructuralRamsey.Girth.CoherentPort.BridgeData.cross_occurrence
#print axioms StructuralRamsey.Girth.CoherentPort.BridgeData.joinTree
#print axioms StructuralRamsey.Girth.CoherentPort.BridgeData.forestOfCopies
#print axioms StructuralRamsey.Girth.CoherentPort.TypedInterfaceForest.sumPort
#print axioms StructuralRamsey.Girth.CoherentPort.TypedInterfaceForest.toForestOfCopies
#print axioms StructuralRamsey.Girth.CoherentPort.joinTree_of_coherent_shared_indices
#print axioms StructuralRamsey.Girth.CoherentPort.typedInterfaceForest_of_coherent_shared_indices
#print axioms StructuralRamsey.Girth.CoherentPort.old_left_midpoints_remain_inside_of_closed_port
#print axioms StructuralRamsey.Girth.CoherentPort.operationClosed_port_iff_sides
#print axioms StructuralRamsey.Girth.CoherentPort.mixed_operation_output_mem_port
#print axioms StructuralRamsey.Girth.CoherentPort.crossing_path3_singleton_port_shape
#print axioms StructuralRamsey.Girth.CoherentPort.only_three_cross_port_P4_types
#print axioms StructuralRamsey.Girth.CoherentPort.crossing_P4_birth_shape_of_closed_port
#print axioms StructuralRamsey.Girth.CoherentPort.crossing_induced_P4_no_endpoint_midpoint
#print axioms StructuralRamsey.Girth.CoherentPort.crossing_induced_P4_no_endpoint_midpoint_reversed
