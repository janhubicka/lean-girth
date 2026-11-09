import Girth.TrainRecursiveSelectedGluingIncidence
import Girth.TrainRecursiveLargeBaseCoarsening
import Girth.ActualActivePartitePresentation
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact gluing incidence before transferring the positive girth certificate

The underlying relational structure of coarsening is definitionally the
same as the lower selected stage.  Its selected partite gluing copies
are indexed by the SAME subtype of designated original copies; their
underlying embeddings are definitionally the same actual embeddings.
Thus we can compare the entire OrderOneData, not just its support girth
or a numerical cutoff.  The generic checked reindexing theorem then
transports every global simultaneous supreme plan, for ALL cutoffs.

The proof is independent of the positive-cut stage certificate: no
ForestTailStage.tailGirth assumption is consumed until a caller uses
this equivalence.  A failure of either definitional equality is now a
small, explicit elaboration failure instead of an implicit change
hidden in a larger recursive proof.

No Hales--Jewett power girth, no additional finite pass, no deletions of
physical ambient A-edges, no identification of equal-copy carriers.
Circulation only; no appendix or manuscript marks.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA P V X : Type v}
variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)

variable {family : Set (Embedding (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A (Old.toRelStructure.induce (activeCarrier A Old α))) t.length}
variable {allowed : Fin (t.length + 1) → Set V}
variable (S : ForestTailStage A (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure family t targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

include hFamilyParts

/-- The underlying A-support edges, actual selected labels and all wagon
parents agree with the original selected lower stage at every cut. -/
theorem ForestTailStage.coarsenedSelected_original_incidence_eq
    (μ : Fin (t.length + 1)) :
    activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family // b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α)
          D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding) S.train μ =
    (selectedPictureOrderOneData A (Old.toRelStructure.induce (activeCarrier A Old α))
      D.toRelStructure S.system family S.selected S.train μ).reindexDesignated
      (Equiv.refl _) := by
  change activeGluingWitnessOrderOneData A Old α
      S.system.toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family // b ∈ S.selected} => i.1.embedding) S.train μ =
    (selectedPictureOrderOneData A (Old.toRelStructure.induce (activeCarrier A Old α))
      D.toRelStructure S.system family S.selected S.train μ).reindexDesignated
      (Equiv.refl _)
  exact activeGluingWitness_eq_reindexed_selectedPicture
    A (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure Old S.system family S.selected α
    (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family // b ∈ S.selected} => i.1.embedding) S.train μ
    (Equiv.refl _) (fun _ => rfl)

/-- Full simultaneous system-girth is equivalent for the two LITERAL
incidence records, at any cut and any cutoff. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_iff_original
    (μ : Fin (t.length + 1)) (q : ℕ) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family // b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α)
          D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding) S.train μ).FullSystemGirthGT q ↔
    (selectedPictureOrderOneData A (Old.toRelStructure.induce (activeCarrier A Old α))
      D.toRelStructure S.system family S.selected S.train μ).FullSystemGirthGT q := by
  rw [S.coarsenedSelected_original_incidence_eq
    A Old α D hFamilyParts μ]
  exact OrderOneData.reindexDesignated_fullSystemGirth_iff
    (selectedPictureOrderOneData A (Old.toRelStructure.induce (activeCarrier A Old α))
      D.toRelStructure S.system family S.selected S.train μ) (Equiv.refl _) q

end StructuralRamsey.Girth.TrainRecursiveWitness
