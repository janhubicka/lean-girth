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

local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)
local notation "Target" =>
  actualActiveSubsystemPartite A Old α

variable {family : Set (Embedding Source D.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source) t.length}
variable {allowed : Fin (t.length + 1) → Set V}
variable (S : ForestTailStage A Source D.toRelStructure family t targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

local notation "Selected" =>
  {b : DesignatedCopy Source D.toRelStructure S.system family //
    b ∈ S.selected}
local notation "Gluing" => fun i : Selected =>
  (selectedPartiteGluingFamily_of_largeBase
    Target D S.system S.isPartite family hFamilyParts
    S.selected i).toEmbedding

include hFamilyParts

/-- No physical A-support edge, source embedding, or selected label is
changed when the genuine lower witness is part-coarsened. -/
theorem ForestTailStage.coarsenedSelected_original_incidence_eq
    (μ : Fin (t.length + 1)) :
    activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      Gluing S.train μ =
    (selectedPictureOrderOneData A Source D.toRelStructure S.system
      family S.selected S.train μ).reindexDesignated (Equiv.refl Selected) := by
  change activeGluingWitnessOrderOneData A Old α
      S.system.toRelStructure
      (fun i : Selected => i.1.embedding) S.train μ =
    (selectedPictureOrderOneData A Source D.toRelStructure S.system
      family S.selected S.train μ).reindexDesignated (Equiv.refl Selected)
  exact activeGluingWitness_eq_reindexed_selectedPicture
    A Source D.toRelStructure Old S.system family S.selected α
    (fun i : Selected => i.1.embedding) S.train μ
    (Equiv.refl Selected) (fun _ => rfl)

/-- Global full-system girth is equivalent for the LITERAL coarsened
selected gluing witnesses and the true selected lower stage at ANY
cutoff.  There is no new girth assumption; it follows from equality
of the complete incidence data with its honest index equivalence. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_iff_original
    (μ : Fin (t.length + 1)) (q : ℕ) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      Gluing S.train μ).FullSystemGirthGT q ↔
    (selectedPictureOrderOneData A Source D.toRelStructure
      S.system family S.selected S.train μ).FullSystemGirthGT q := by
  rw [S.coarsenedSelected_original_incidence_eq A Old α D hFamilyParts μ]
  exact OrderOneData.reindexDesignated_fullSystemGirth_iff
    (selectedPictureOrderOneData A Source D.toRelStructure
      S.system family S.selected S.train μ) (Equiv.refl Selected) q

end StructuralRamsey.Girth.TrainRecursiveWitness
