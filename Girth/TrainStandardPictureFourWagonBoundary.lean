import Girth.TrainFourWagonFrameBuilder
import Girth.TrainStandardPictureSystemGirth
import Girth.ActiveCarrierStrong
import Girth.TrainSharedOldACarrierCoreEmbedding

/-!
# Circulation: from the genuine old four-wagon frame to a core support edge

The finite-cycle argument and the actual boundary geometry now compose.
A four-occurrence frame in the genuine old standard-picture model, with
both vertex connectors in the true active subsystem, supplies a physical
old A-edge through them. A-strongness of that subsystem absorbs the WHOLE
edge. The existing shared-to-core map then transports its entire carrier
to a genuine core A-support edge.

This avoids redoing active-boundary classification for every physical
A-edge. In the finite ordered setting active strongness is already a
consequence of partiteness over an A-linear base, not an extra assumption.

The remaining two-standard task is to construct this old frame from the
OUTPUT configuration and the witness long pieces. Neither that assembly
nor general cycle transfer is asserted here. No appendix result is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y J : Type v}

/-- Strongness absorbs an entire genuine physical support edge as soon
as it contains two distinct vertices of the strong carrier. -/
theorem oldACarrier_subset_of_two_mem_aStrong
    (A : RelStructure L UA) (R : RelStructure L X)
    (S : Set X) (hStrong : AStrong A R S)
    (edge : OldACarrierEdge A R)
    (x y : X) (hxy : x ≠ y)
    (hxEdge : x ∈ edge.1) (hyEdge : y ∈ edge.1)
    (hxS : x ∈ S) (hyS : y ∈ S) :
    edge.1 ⊆ S := by
  rcases edge.2 with ⟨a, ha⟩
  rw [ha] at hxEdge hyEdge ⊢
  apply hStrong a
  intro hSmall
  exact hxy (hSmall ⟨hxEdge, hxS⟩ ⟨hyEdge, hyS⟩)

section StandardPicture

variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (μ : Fin (m + 1))

/-- Instantiate the finite four-occurrence contradiction on actual old
vertices, designated copies, support carriers and wagon quotients.
The boundary-pair premise is discharged, not passed as an abstract axiom. -/
theorem standardPicture_fourWagonFrame_pairEdge
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (e : RelStructure.Embedding A D)
    (F : (standardPictureOrderOneData A B D C family T μ).FourWagonFrame)
    (hFull : (standardPictureOrderOneData A B D C family T μ).FullSystemGirthGT 2)
    (hx : F.x ∈ activeCarrier A C e.toFunctionEmbedding)
    (hy : F.y ∈ activeCarrier A C e.toFunctionEmbedding) :
    (standardPictureOrderOneData A B D C family T μ).PairEdge F.x F.y := by
  apply F.pairEdge_of_system_bound_and_boundary
    (standardPictureOrderOneData A B D C family T μ) hFull
    (standardPictureOrderOneData_copyEdgeCarrierCompatible A B D C family T μ)
  intro q hxCopy hyCopy
  exact standardPictureOrderOneData_pairEdge_of_two_active
    A B D C family T μ hStrong e q F.x F.y F.hxy hxCopy hyCopy hx hy

/-- The old edge is genuinely SHARED: its full carrier, not only its two
connectors, lies in the active subsystem. -/
theorem standardPicture_fourWagonFrame_sharedEdge
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (e : RelStructure.Embedding A D)
    (hActive : AStrong A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding))
    (F : (standardPictureOrderOneData A B D C family T μ).FourWagonFrame)
    (hFull : (standardPictureOrderOneData A B D C family T μ).FullSystemGirthGT 2)
    (hx : F.x ∈ activeCarrier A C e.toFunctionEmbedding)
    (hy : F.y ∈ activeCarrier A C e.toFunctionEmbedding) :
    ∃ edge : SharedOldACarrierEdge A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding),
      F.x ∈ edge.1.1 ∧ F.y ∈ edge.1.1 := by
  obtain ⟨edge, hxEdge, hyEdge⟩ :=
    standardPicture_fourWagonFrame_pairEdge
      A B D C family T μ hStrong e F hFull hx hy
  exact ⟨⟨edge, oldACarrier_subset_of_two_mem_aStrong
    A C.toRelStructure (activeCarrier A C e.toFunctionEmbedding)
    hActive edge F.x F.y F.hxy hxEdge hyEdge hx hy⟩, hxEdge, hyEdge⟩

/-- Transport the shared edge to an ACTUAL core support carrier. The
physical images of both original connectors belong to that core image. -/
theorem standardPicture_fourWagonFrame_coreEdge
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (e : RelStructure.Embedding A D)
    (hActive : AStrong A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding))
    (F : (standardPictureOrderOneData A B D C family T μ).FourWagonFrame)
    (hFull : (standardPictureOrderOneData A B D C family T μ).FullSystemGirthGT 2)
    (hx : F.x ∈ activeCarrier A C e.toFunctionEmbedding)
    (hy : F.y ∈ activeCarrier A C e.toFunctionEmbedding)
    (R : RelStructure L Y)
    (f : J → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
    (i : J) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let std := RelStructure.Attachment.copyEmbedding C.toRelStructure S R f i
    let core := RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
    ∃ edge : OldACarrierEdge A R,
      std F.x ∈ ((fun y : Y => core y) '' edge.1) ∧
      std F.y ∈ ((fun y : Y => core y) '' edge.1) := by
  dsimp only
  obtain ⟨edge, hxEdge, hyEdge⟩ :=
    standardPicture_fourWagonFrame_sharedEdge
      A B D C family T μ hStrong e hActive F hFull hx hy
  refine ⟨sharedOldACarrierCoreMap
    A C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i edge,
    ?_, ?_⟩
  · rw [← sharedOldACarrierCoreMap_image
      A C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i edge]
    exact ⟨F.x, hxEdge, rfl⟩
  · rw [← sharedOldACarrierCoreMap_image
      A C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i edge]
    exact ⟨F.y, hyEdge, rfl⟩

end StandardPicture

/-- In the manuscript's finite ordered setting, active strongness follows
from the previously verified geometry; only the actual old frame remains
to be constructed from the output two-standard configuration. -/
theorem standardPicture_fourWagonFrame_sharedEdge_ordered
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (B : RelStructure L.withOrder VB) (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (family : Set (RelStructure.Embedding B D))
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A₀.ordered C.toRelStructure) m)
    (μ : Fin (m + 1))
    (hPartite : C.IsPartiteOver D)
    (hLinear : ALinear A₀.ordered D)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A₀.ordered D (copyCarrier b))
    (e : RelStructure.Embedding A₀.ordered D)
    (F : (standardPictureOrderOneData A₀.ordered B D C family T μ).FourWagonFrame)
    (hFull : (standardPictureOrderOneData A₀.ordered B D C family T μ).FullSystemGirthGT 2)
    (hx : F.x ∈ activeCarrier A₀.ordered C e.toFunctionEmbedding)
    (hy : F.y ∈ activeCarrier A₀.ordered C e.toFunctionEmbedding) :
    ∃ edge : SharedOldACarrierEdge A₀.ordered C.toRelStructure
        (activeCarrier A₀.ordered C e.toFunctionEmbedding),
      F.x ∈ edge.1.1 ∧ F.y ∈ edge.1.1 := by
  exact standardPicture_fourWagonFrame_sharedEdge
    A₀.ordered B D C family T μ hStrong e
    (activeCarrier_aStrong_ordered A₀ D C hPartite hLinear e)
    F hFull hx hy

end StructuralRamsey.Girth
