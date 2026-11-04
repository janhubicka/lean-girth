import Girth.TrainRecursiveActualFineInputs

/-!
Track D axiom provenance probe (2026-11-04).

The assembled conclusion unexpectedly reports sorryAx on the exact-head
Lean gate, despite its two direct source lemmas having passed earlier
audits. Print those direct dependencies and the nontrivial data terms
that enter their specialization before the assembled theorem. This is
diagnostic only; a green focused build is not certification while the
assembled conclusion reports sorryAx.
-/

#print axioms StructuralRamsey.Girth.activeSourcePart
#print axioms StructuralRamsey.Girth.actualActiveSubsystemPartite
#print axioms StructuralRamsey.Partite.System.coarsenVia
#print axioms StructuralRamsey.Girth.selectedPartiteGluingFamily_of_largeBase
#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.ForestTailStage.trueActive_irreduciblesExtendTo
#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.ForestTailStage.coarsenedSelected_fineWitnessInputs
#print axioms StructuralRamsey.Girth.TrainRecursiveWitness.ForestTailStage.coarsenedFineInputs_of_trueActive
