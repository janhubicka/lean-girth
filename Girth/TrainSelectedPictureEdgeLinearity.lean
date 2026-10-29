import Girth.TrainSelectedPictureWagonPairGeometry
import Girth.TrainSelectedPictureCorePairGeometry

set_option Elab.async false

/-!
# Linearity of the actual support edges

Localize one actual support edge to a core or standard source. Whole-piece
strongness puts any edge sharing two of its vertices in that same piece.
The physical edge pullback then reduces equality to source edge linearity.
This supplies the edge half of output LinearPretrain without a new gluing-image
strongness hypothesis; wagon-carrier linearity is proved separately.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section EdgeLinearity

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Vertex" => RelStructure.Attachment.Vertex S (W := Y) (I := I)
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "CoreCar" => attachedCoreAEdgeCarrier A C.toRelStructure S R f
local notation "Eqv" => actualAPictureEdgeEquiv A hA C.toRelStructure S R f
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S) Emb i a))
local notation "CoreActual" => (fun (a : CoreEdge) =>
  Eqv (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I a))
local notation "Old" => selectedPictureOrderOneData A B D C family selected T μ
local notation "Witness" => sharedWitnessOrderOneData U μ Emb CoreCar
include hA

/-- The full actual support-edge family is linear under source edge linearity
and strongness of the whole active subsystem and attached standards. This
uses no wagon-girth bound, exact shared train relation, or output linearity. -/
theorem attachedSelectedPicture_edge_carriers_inter_subsingleton
    (hOld : (Old).LinearPretrain) (hCore : (Witness).LinearPretrain)
    (hActive : AStrong A C.toRelStructure S)
    (hStd : ∀ i : I, AStrong A Actual (copyCarrier (Std i)))
    (a b : ActualEdge) (hab : a ≠ b) : (a.1 ∩ b.1).Subsingleton := by
  classical
  intro x hx y hy
  by_contra hxy
  have hCover (g : ActualEdge) :
      (∃ r : CoreEdge, g = CoreActual r) ∨
        ∃ i : I, ∃ r : OldEdge, g = StdEdge i r := by
    rcases physicalPictureEdge_covered
      (sharedOldACarrierInclusion A C.toRelStructure S) Emb ((Eqv).symm g)
      with ⟨r, hr⟩ | ⟨i, r, hr⟩
    · exact Or.inl ⟨r, ((Eqv).apply_symm_apply g).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv p) hr)⟩
    · exact Or.inr ⟨i, r, ((Eqv).apply_symm_apply g).symm.trans
        (congrArg (fun p : ActualAPicturePushoutEdge A C.toRelStructure S R I => Eqv p) hr)⟩
  rcases hCover a with ⟨r, rfl⟩ | ⟨i, r, rfl⟩
  · have hCarrier (t : CoreEdge) : (CoreActual t).1 = CoreCar t :=
      actualAPictureEdgeEquiv_core_carrier A hA C.toRelStructure S R f t
    have hSub : (CoreActual r).1 ⊆ copyCarrier CoreEmb := by
      intro z hz
      rw [hCarrier] at hz
      obtain ⟨w, _hw, hwz⟩ := hz
      exact ⟨w, hwz⟩
    have hbSub : b.1 ⊆ copyCarrier CoreEmb :=
      oldACarrier_subset_of_two_mem_aStrong A Actual (copyCarrier CoreEmb)
        (attachment_core_aStrong C.toRelStructure S R f hA hActive)
        b x y hxy hx.2 hy.2 (hSub hx.1) (hSub hy.1)
    obtain ⟨s, rfl⟩ := actualASupport_core_edge_pullback
      A hA C.toRelStructure S R f b hbSub
    have hrs : r ≠ s := fun h => hab (congrArg CoreActual h)
    apply hxy
    apply hCore.1 r s hrs
    · exact ⟨by simpa only [sharedWitnessOrderOneData, hCarrier] using hx.1,
        by simpa only [sharedWitnessOrderOneData, hCarrier] using hx.2⟩
    · exact ⟨by simpa only [sharedWitnessOrderOneData, hCarrier] using hy.1,
        by simpa only [sharedWitnessOrderOneData, hCarrier] using hy.2⟩
  · have hMem (t : OldEdge) (z : Vertex) (hz : z ∈ (StdEdge i t).1) :
        z ∈ (fun w : X => Std i w) '' t.1 :=
      Eq.mp (congrArg (fun Z : Set Vertex => z ∈ Z)
        (actualAPictureEdgeEquiv_standard_carrier A hA C.toRelStructure S R f i t)) hz
    have hSub : (StdEdge i r).1 ⊆ copyCarrier (Std i) := by
      intro z hz
      obtain ⟨w, _hw, hwz⟩ := hMem r z hz
      exact ⟨w, hwz⟩
    have hbSub : b.1 ⊆ copyCarrier (Std i) :=
      oldACarrier_subset_of_two_mem_aStrong A Actual (copyCarrier (Std i))
        (hStd i) b x y hxy hx.2 hy.2 (hSub hx.1) (hSub hy.1)
    obtain ⟨s, rfl⟩ := attachedSelectedPicture_geometric_edge_pullback
      A hA D C e R f i b hbSub
    have hrs : r ≠ s := fun h => hab (congrArg (StdEdge i) h)
    obtain ⟨x₀, hxr, hxx⟩ := hMem r x hx.1
    obtain ⟨y₀, hyr, hyy⟩ := hMem r y hy.1
    have hxs : x₀ ∈ s.1 := by
      obtain ⟨z, hz, hzx⟩ := hMem s x hx.2
      have hzx₀ : z = x₀ := (Std i).injective (hzx.trans hxx.symm)
      exact Eq.mp (congrArg (fun t : X => t ∈ s.1) hzx₀) hz
    have hys : y₀ ∈ s.1 := by
      obtain ⟨z, hz, hzy⟩ := hMem s y hy.2
      have hzy₀ : z = y₀ := (Std i).injective (hzy.trans hyy.symm)
      exact Eq.mp (congrArg (fun t : X => t ∈ s.1) hzy₀) hz
    have hxy₀ : x₀ = y₀ := hOld.1 r s hrs ⟨hxr, hxs⟩ ⟨hyr, hys⟩
    exact hxy (hxx.symm.trans ((congrArg (fun z : X => Std i z) hxy₀).trans hyy))

end EdgeLinearity

end StructuralRamsey.Girth
