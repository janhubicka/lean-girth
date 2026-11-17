import Girth.TrainActualBottomDesignatedBoundary
import Girth.AttachmentStrongness

set_option autoImplicit false
set_option Elab.async false

/-!
# Different geometric owners have their overlap entirely in the core

In the actual free attachment, an occurrence owned by standard i is
physically contained in that standard. An occurrence with core-edge
owner is literally the corresponding physical core support edge.
Different standards intersect only in the core; a core edge is wholly
inside it. Thus distinct GEOMETRIC owners imply the intersection of
the two original occurrence carriers is in the actual shared core.

This is source-label geometry. The labels themselves are NEVER
identified with their owner indices.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section BottomGeometricCoreSeparation

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Core" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

/-- The literal core-edge owner is carried by the full core image,
irrespective of any chosen standard which may also contain it. -/
theorem attachedSelectedPicture_bottom_coreOwner_subset_core
    (b : CoreEdge) :
    (Out).carrier (Sum.inr (CoreActual b)) ⊆ copyCarrier Core := by
  rw [show (Out).carrier (Sum.inr (CoreActual b)) = (CoreActual b).1 from rfl]
  rw [actualAPictureEdgeEquiv_core_carrier
    A hA C.toRelStructure S R f b]
  change ((fun y : Y => Core y) '' b.1) ⊆ copyCarrier Core
  rintro z ⟨y, _hy, rfl⟩
  exact ⟨y, rfl⟩

/-- A genuine output label whose chosen *geometric* owner is a core
edge has its entire carrier in the core, not merely its boundary. -/
theorem attachedSelectedPicture_bottom_geometric_coreOwner_subset_core
    (a : (I × {q : DesignatedCopy B D C family // q ∈ selected}) ⊕ ActualEdge)
    (b : CoreEdge)
    (hAllowed : GeomAllowed a (Sum.inr b)) :
    (Out).carrier a ⊆ copyCarrier Core := by
  change a = Sum.inr (CoreActual b) at hAllowed
  rw [hAllowed]
  exact attachedSelectedPicture_bottom_coreOwner_subset_core
    A hA B D C family selected e R f T U hShared b

/-- Two distinct geometric owners have no original carrier overlap
outside the actual core. The actual B-label is NOT replaced by its
standard owner, and shared A-edges retain their literal carriers. -/
theorem attachedSelectedPicture_bottom_distinctOwners_intersection_core
    (a b : (I × {q : DesignatedCopy B D C family // q ∈ selected}) ⊕ ActualEdge)
    (ownerA ownerB : I ⊕ CoreEdge)
    (ha : GeomAllowed a ownerA)
    (hb : GeomAllowed b ownerB)
    (hDifferent : ownerA ≠ ownerB) :
    (Out).carrier a ∩ (Out).carrier b ⊆ copyCarrier Core := by
  intro z hz
  cases hAOwner : ownerA with
  | inr c =>
      have hSub :=
        attachedSelectedPicture_bottom_geometric_coreOwner_subset_core
          A hA B D C family selected e R f T U hShared a c (by
            rw [hAOwner] at ha
            exact ha)
      exact hSub hz.1
  | inl i =>
      cases hBOwner : ownerB with
      | inr c =>
          have hSub :=
            attachedSelectedPicture_bottom_geometric_coreOwner_subset_core
              A hA B D C family selected e R f T U hShared b c (by
                rw [hBOwner] at hb
                exact hb)
          exact hSub hz.2
      | inl j =>
          have hij : i ≠ j := by
            intro heq
            exact hDifferent (by rw [hAOwner, hBOwner, heq])
          have haSub : (Out).carrier a ⊆ copyCarrier (Std i) := by
            rw [hAOwner] at ha
            exact ha
          have hbSub : (Out).carrier b ⊆ copyCarrier (Std j) := by
            rw [hBOwner] at hb
            exact hb
          exact attachment_copy_copy_intersection_subset_core
            C.toRelStructure S R f hij
              ⟨haSub hz.1, hbSub hz.2⟩

end BottomGeometricCoreSeparation
end StructuralRamsey.Girth
