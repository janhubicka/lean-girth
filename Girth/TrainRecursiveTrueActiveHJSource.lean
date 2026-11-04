import Girth.TrainRecursiveActivePartite
import Girth.ForestActualRecursiveSupport
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# All three Hales--Jewett source hypotheses hold in the genuine active fibre

The larger Ramsey base in the nontrivial q>2 recursion uses an induced
Hales--Jewett power of the true active A-partite target. Three
properties of that source are needed: it is genuinely partite over
A, its physical A-copies are A-linear, and every physical vertex
belongs to a genuine A-copy.

All three properties follow from the OLD ForestTailStage with no
new local witness and no high-girth assumption: partiteness follows
from restriction to the actual projected active carrier; A-linearity
is hereditary under induced substructures; and the active carrier
is defined by membership in genuine projected A-copies.

The result does NOT claim any girth property of the HJ power, nor
strongness of HJ lines (which is a separate geometric theorem).
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The TRUE active source has all three elementary prerequisites for
the induced HJ base construction. The stage's complete A-support
is not modified, and no selected-copy ownership is inferred. -/
theorem ForestTailStage.trueActive_HJ_sourceGeometry
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D) :
    (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).IsPartiteOver A ∧
    ALinear A
      (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure ∧
    (∀ x : activeCarrier A stage.system e.toFunctionEmbedding,
      ∃ a : Embedding A
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding).toRelStructure,
        x ∈ copyCarrier a) := by
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  refine ⟨actualActiveSubsystemPartite_isPartiteOver
    A D stage.system stage.isPartite e, ?_, ?_⟩
  · change ALinear A (stage.system.toRelStructure.induce S)
    exact aLinear_induce stage.aLinear S
  · intro x
    obtain ⟨h, hh, hx⟩ :=
      actualRecursiveActiveSupport_cover
        A stage.system e.toFunctionEmbedding x
    obtain ⟨a, rfl⟩ := hh
    exact ⟨a, hx⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
