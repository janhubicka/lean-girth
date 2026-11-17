import Girth.TrainFillingPrivateCompletedWPrivateEHN

set_option Elab.async false

/-!
# Track 5: genuine completed-W EHN proof gate

This is independent of the much larger full Track 5
OrderStage/filling integration. The source first-wagon
relational order is completed across summands, while its
small hyperedges remain componentwise.

On the exact branch head, run:
  LEAN_NUM_THREADS=1 lake env lean Girth/CheckTrack5CompletedW.lean

Then inspect the full #print axioms output. The presence of
this gate is NOT a kernel certificate. No new theorem in
the imported completed-W chain is validated yet.
-/

#check StructuralRamsey.Girth.completedFirstWagon_intraColour_order_iff
#check StructuralRamsey.Girth.completedFirstWagonSummandEmbedding
#check StructuralRamsey.Girth.completedFirstWagon_ACopy_subset_summand
#check StructuralRamsey.Girth.completedFirstWagonSummand_aStrong
#check StructuralRamsey.Girth.completedFirstWagon_supportCopies_iff
#check StructuralRamsey.Girth.completedFirstWagon_covered
#check StructuralRamsey.Girth.completedFirstWagon_aLinear
#check StructuralRamsey.Girth.completedFirstWagon_order_of_colour_lt
#check StructuralRamsey.Girth.completedFirstWagonSummand_strictMono
#check StructuralRamsey.Girth.completedFirstWagon_allACopies_strictMono
#check StructuralRamsey.Girth.completedFirstWagon_orderedEHN
#check StructuralRamsey.Girth.completedFirstWagon_privateEHN

#print axioms StructuralRamsey.Girth.completedFirstWagonSummandEmbedding
#print axioms StructuralRamsey.Girth.completedFirstWagonSummand_aStrong
#print axioms StructuralRamsey.Girth.completedFirstWagon_supportCopies_iff
#print axioms StructuralRamsey.Girth.completedFirstWagon_covered
#print axioms StructuralRamsey.Girth.completedFirstWagon_aLinear
#print axioms StructuralRamsey.Girth.completedFirstWagonSummand_strictMono
#print axioms StructuralRamsey.Girth.completedFirstWagon_allACopies_strictMono
#print axioms StructuralRamsey.Girth.completedFirstWagon_orderedEHN
#print axioms StructuralRamsey.Girth.completedFirstWagon_privateEHN
