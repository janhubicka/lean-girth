import Girth.TrainRecursiveCoarsenedRamseyArrow
import Girth.TrainRecursiveActivePartite

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact fine train restriction for genuinely selected partite gluing copies

The lower forest-tail witness is equipped with an actual
targetRestriction field: the whole source train is preserved and
reflected by each of its selected designated copies.

When the lower target is the literal true active induced source and
the lower Ramsey base is a larger A-partite system, coarsening part
labels turns the selected designated copies into the genuine
A-partite gluing embeddings. Their underlying relational embeddings
and their physical support edges do not change. Hence the lower
targetRestriction is exactly the fine-restriction clause expected by
the Track B attachment construction.

This lemma does NOT assert the existence of the lower stage, a
particular refinement target train, fine parameter bounds or
positive gluing full-system girth. It preserves all labels and does
not quotient equal vertex carriers.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P V X : Type v}
variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)

local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)
/-- Full preservation and reflection of all physical fine train
cuts on each actual selected gluing embedding after part-coarsening.
No prescribed target cut or selected copy is replaced by an arbitrary
projected copy. The selected indices remain the literal subtype. -/
theorem ForestTailStage.coarsenedSelected_trainRestriction
    (ν : Fin (t.length + 1))
    (i : {q : DesignatedCopy Source D.toRelStructure S.system family //
      q ∈ S.selected}) (a b : Embedding A Source) :
    S.train.rel ν
      (actualEdge ((selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A Old α) D S.system S.isPartite
        family hFamilyParts S.selected i).toEmbedding.comp a))
      (actualEdge ((selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A Old α) D S.system S.isPartite
        family hFamilyParts S.selected i).toEmbedding.comp b)) ↔
    targetTrain.rel ν (actualEdge a) (actualEdge b) :=
  S.targetRestriction i.1 i.2 ν a b

end StructuralRamsey.Girth.TrainRecursiveWitness
