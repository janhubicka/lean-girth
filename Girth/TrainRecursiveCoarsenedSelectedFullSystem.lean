import Girth.TrainRecursiveLargeBaseCoarsening
import Girth.TrainRecursiveWitnessPass
import Girth.TrainRecursiveActivePartite
import Girth.TrainActiveGluingWitness

set_option autoImplicit false

/-!
# Actual positive full-system certificates for a larger-base selected gluing family

A lower forest-tail stage may use a larger Q-partite Ramsey base D,
yet its source is exactly the true active induced relational target.
Its selected labels are genuine target copies over D, not an ad-hoc
family of images or a quotient by coincident carriers.

If each selected base embedding respects the coarse A-parts, #773
turns precisely those selected labels into genuine A-partite gluing
maps after coarsening the lower witness.  These maps have the SAME
underlying relational embeddings as the selected copies.

Consequently the complete gluing OrderOneData record at each positive
fine cut is literally the lower stage's selected-picture OrderOneData.
The existing stage tailGirth certificate transfers to full-system
girth for the canonical, truly PARTITE gluing family and can be
lowered to a smaller cutoff.  This is the missing certificate interface
needed by Track B's actual fine-witness attachment bounds.

The existence of the lower stage, its correctly Q-partite base/family,
the fine train's exact restriction and allowed geometry, and the
attached output's indexed SupremeCycleBound remain independent open
obligations. No ambient edge or designated label is removed here.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)
local notation "Source" => Old.toRelStructure.induce (activeCarrier A Old α)
local notation "Target" => actualActiveSubsystemPartite A Old α

variable (family : Set (Embedding Source D.toRelStructure))
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source) t.length}
variable {allowed : Fin (t.length + 1) → Set V}
variable (S : ForestTailStage A Source D.toRelStructure family t targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family → ∀ x : activeCarrier A Old α,
  D.part (b x) = activeSourcePart A Old α x)

local notation "Selected" =>
  {q : DesignatedCopy Source D.toRelStructure S.system family // q ∈ S.selected}
local notation "PartiteGluing" =>
  selectedPartiteGluingFamily_of_largeBase
    Target D S.system S.isPartite family hFamilyParts S.selected

/-- At every positive stage coordinate, the actual PARTITE gluing family
obtained by coarsening has the exact full system-girth cutoff of the
lower selected-picture stage. This is a complete indexed incidence
certificate, including global simultaneous legal replacement plans. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_at_positive
    (j : Fin t.length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : Selected => (PartiteGluing i).toEmbedding)
      S.train j.castSucc).FullSystemGirthGT (t.get j) := by
  change (selectedPictureOrderOneData A Source D.toRelStructure
    S.system family S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
  exact S.tailGirth j hj

/-- The actual fine gluing system certificate is monotone in its numerical
cutoff; in the recursive vector this lets the inserted and retained
coordinates be instantiated with their respective requested bounds. -/
theorem ForestTailStage.coarsenedSelected_fullSystem_at_positive_mono
    (j : Fin t.length) (hj : 0 < j.val)
    (q : ℕ) (hq : q ≤ t.get j) :
    (activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : Selected => (PartiteGluing i).toEmbedding)
      S.train j.castSucc).FullSystemGirthGT q := by
  change (selectedPictureOrderOneData A Source D.toRelStructure
    S.system family S.selected S.train j.castSucc).FullSystemGirthGT q
  have hFull : (selectedPictureOrderOneData A Source D.toRelStructure
      S.system family S.selected S.train j.castSucc).FullSystemGirthGT (t.get j) :=
    S.tailGirth j hj
  refine ⟨hFull.1, ?_⟩
  intro n K hAccept hOrder
  exact hFull.2 n K hAccept (by omega)

end StructuralRamsey.Girth.TrainRecursiveWitness
