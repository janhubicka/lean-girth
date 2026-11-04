import Girth.TrainRecursiveLargeBaseCutParameters
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual lower-stage adjacent parameters after part coarsening

The genuine lower ForestTailStage stores an adjacent-parameter proof
for the complete physical A-edge train. Coarsening only the part map
does not change the edge family, wagon quotient, or parent maps.

If the lower base allowed sets map into a prescribed family of
fine A-part sets, the same train has the correct coarsened parameters.
There is also a canonical choice: the image of each lower allowed
set under the larger base's A-part map. No separate adjacent-parameter
record is needed for this choice.

This does not assert the singleton-parent or first/retained allowed
set containments required by the recursive fine-witness constructor.
Those require appropriate choices of lower allowed sets in the
induction, not merely coarsening. No new lower witness is constructed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The lower forest-stage's actual parameter field yields every desired
coarsened allowed set which contains the images of lower base
permitted sets. No physical support edge is pruned. -/
theorem ForestTailStage.coarsened_adjacentParameters_of_allowed
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : StructuralRamsey.Partite.System L UA P)
    {family : Set (Embedding B D.toRelStructure)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D.toRelStructure family t targetTrain allowed)
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (hAllowed : ∀ ν, allowed ν ⊆ D.part ⁻¹' fineAllowed ν) :
    S.train.AdjacentParameters (fun edge => edge.1)
      (fun ν => (S.system.coarsenVia D S.isPartite).part ⁻¹' fineAllowed ν) := by
  exact S.train.adjacentParameters_after_baseCoarsening
    A D S.system S.isPartite allowed fineAllowed S.parameters hAllowed

/-- If the lower recursion is invoked with the inverse images of
the prescribed fine A-part sets, its actual stage parameters become
exactly the desired fine parameters after coarsening. This eliminates
both the parameter input and the image-containment premise in the
chosen lower-rank invocation. -/
theorem ForestTailStage.coarsened_adjacentParameters_preimage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : StructuralRamsey.Partite.System L UA P)
    {family : Set (Embedding B D.toRelStructure)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (S : ForestTailStage A B D.toRelStructure family t targetTrain
      (fun ν => D.part ⁻¹' fineAllowed ν)) :
    S.train.AdjacentParameters (fun edge => edge.1)
      (fun ν => (S.system.coarsenVia D S.isPartite).part ⁻¹' fineAllowed ν) := by
  apply S.coarsened_adjacentParameters_of_allowed A B D fineAllowed
  intro ν p hp
  exact hp

/-- The canonical family of coarsened allowed parts is obtained
by taking images of the actual lower base's permitted part sets.
All train relations remain unchanged, including the top. -/
theorem ForestTailStage.coarsened_adjacentParameters_image
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : StructuralRamsey.Partite.System L UA P)
    {family : Set (Embedding B D.toRelStructure)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D.toRelStructure family t targetTrain allowed) :
    S.train.AdjacentParameters (fun edge => edge.1)
      (fun ν => (S.system.coarsenVia D S.isPartite).part ⁻¹'
        (D.part '' allowed ν)) := by
  apply S.coarsened_adjacentParameters_of_allowed A B D
    (fun ν => D.part '' allowed ν)
  intro ν p hp
  exact ⟨p, hp, rfl⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
