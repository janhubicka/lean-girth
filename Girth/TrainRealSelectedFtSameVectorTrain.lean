import Girth.TrainRecursiveSelectedSharedCoreTrain
import Girth.TrainRecursiveCoarsenedGluingIdentity
import Girth.TrainRecursiveSelectedLowerActualInputs

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual selected same-vector F_t stage: exact original shared-train reflection

The checked selectedSharedCore_train_iff_of_actualLower proves every
shared relation from the lower stage's literal targetRestriction when
the lower target train is the double physical restriction of the old
train to the genuine induced active subsystem.

In the coarsened selected local witness, the gluing index is precisely
the selected lower designated-copy subtype. Coarsening the A-part map
does NOT change its underlying relational embedding or any physical
A-edge. Therefore the existing checked theorem supplies the full hRel
interface of the actual bottom/positive attachment argument, at ALL
cuts including equality bottom and universal top. No separate
transport/identification axiom, first-cut duplicate, or witness girth
assumption is necessary.

The lower stage itself is an actual F_t selected witness; this theorem
does not construct that stage or claim the final finite Ramsey pass.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

/-- A genuine coarsened selected F_t stage with the LITERAL
same-vector restricted old train supplies exact relation
preservation and REFLECTION for every shared physical A-edge
and every old cut. The selected label and carrier are unchanged. -/
theorem ForestTailStage.sameVectorSelected_oldSharedTrain_iff
    (A : RelStructure L UA)
    (Old : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (Large : StructuralRamsey.Partite.System L UA V)
    {t : List ℕ}
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A Old.toRelStructure)
      t.length)
    {family : Set (Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure)}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (lower : ForestTailStage A
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure family t
      (((oldTrain.restrict
          (sharedOldACarrierInclusion A Old.toRelStructure
            (activeCarrier A Old α))).restrict
          (inducedACarrierToShared A Old.toRelStructure
            (activeCarrier A Old α))))
      (fun ν => Large.part ⁻¹' fineAllowed ν))
    (hFamilyParts : ∀ b, b ∈ family →
      ∀ x : activeCarrier A Old α,
        Large.part (b x) = activeSourcePart A Old α x) :
    let E := lower.system.coarsenVia Large lower.isPartite
    let I := {b : DesignatedCopy
      (Old.toRelStructure.induce (activeCarrier A Old α))
      Large.toRelStructure lower.system family // b ∈ lower.selected}
    let f : I → Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        (actualActiveSubsystemPartite A Old α)
        Large lower.system lower.isPartite family hFamilyParts
        lower.selected i).toEmbedding
    ∀ (μ : Fin (t.length + 1)) (i : I)
      (p q : SharedOldACarrierEdge A Old.toRelStructure
        (activeCarrier A Old α)),
      oldTrain.rel μ p.1 q.1 ↔
        lower.train.rel μ
          (sharedOldACarrierCoreEmbedding A Old.toRelStructure
            (activeCarrier A Old α) E.toRelStructure f i p)
          (sharedOldACarrierCoreEmbedding A Old.toRelStructure
            (activeCarrier A Old α) E.toRelStructure f i q) := by
  let S := activeCarrier A Old α
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy
    (Old.toRelStructure.induce S)
    Large.toRelStructure lower.system family // b ∈ lower.selected}
  let f : I → Embedding (Old.toRelStructure.induce S) E.toRelStructure :=
    fun i => (selectedPartiteGluingFamily_of_largeBase
      (actualActiveSubsystemPartite A Old α)
      Large lower.system lower.isPartite family hFamilyParts
      lower.selected i).toEmbedding
  dsimp only
  intro μ i p q
  have h := lower.selectedSharedCore_train_iff_of_actualLower
    A Old.toRelStructure S Large.toRelStructure
    (oldTrain.restrict (sharedOldACarrierInclusion A Old.toRelStructure S))
    (fun ν => Large.part ⁻¹' fineAllowed ν)
    μ i p q
  exact h

end StructuralRamsey.Girth.TrainRecursiveWitness
