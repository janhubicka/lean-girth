import Girth.TrainStandardPictureSystemGirth

/-!
# Circulation: the general four-cycle contradiction in an old picture

This composes the CHECKED finite four-occurrence cycle theorem with
the ACTUAL old standard-picture incidence model.

Assume the old standard picture has system girth > 2 for its genuine
A-support edge labels and projected designated B-copy labels, and
that every prescribed base B-copy is A-strong. If a four-wagon frame
occurs in the old picture with its two vertex connectors in the
true active subsystem, the physical old support hypergraph MUST
have a genuine A-edge containing both connectors.

There is no separate source-edge-carrier coherence axiom and no
unproved boundary-pair-to-edge premise: both follow from the
actual old picture and its active-boundary classification.

The remaining actual picture-step obligations are to construct the
four-wagon frame from two different standard copies and to transfer
an old physical A-edge through the shared pair back to a core H-edge.
The final cycle-transfer theorem and appendix are not addressed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X : Type v}

/-- Complete intrinsic four-occurrence obstruction on the true
standard-picture labels. Under actual A-strong projected copies,
its boundary-pair-to-old-edge hypothesis is automatic. -/
theorem standardPicture_fourWagonFrame_pairEdge
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (μ : Fin (m + 1))
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (e : RelStructure.Embedding A D)
    (F : (standardPictureOrderOneData A B D C family T μ).FourWagonFrame)
    (hFull :
      (standardPictureOrderOneData A B D C family T μ).FullSystemGirthGT 2)
    (hxActive : F.x ∈ activeCarrier A C e.toFunctionEmbedding)
    (hyActive : F.y ∈ activeCarrier A C e.toFunctionEmbedding) :
    (standardPictureOrderOneData A B D C family T μ).PairEdge F.x F.y := by
  let M := standardPictureOrderOneData A B D C family T μ
  have hCompat : M.CopyEdgeCarrierCompatible :=
    standardPictureOrderOneData_copyEdgeCarrierCompatible
      A B D C family T μ
  have hBoundary : ∀ q : DesignatedCopy B D C family,
      F.x ∈ M.copyCarrier q →
      F.y ∈ M.copyCarrier q →
      M.PairEdge F.x F.y := by
    intro q hx hy
    exact standardPictureOrderOneData_pairEdge_of_two_active
      A B D C family T μ hStrong e q F.x F.y F.hxy
      hx hy hxActive hyActive
  exact OrderOneData.FourWagonFrame.pairEdge_of_system_bound_and_boundary
    M F hFull hCompat hBoundary

end StructuralRamsey.Girth
