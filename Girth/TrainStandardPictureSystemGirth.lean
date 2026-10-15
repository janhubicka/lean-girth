import Girth.TrainFourOccurrenceWagonCycle
import Girth.DesignatedPicture
import Girth.ActiveBoundary
import Girth.TrainActualSharedACarrierSubfamily

/-!
# Circulation: genuine standard-picture system-girth incidence data

The four-occurrence argument of the circulated manuscript takes place
INSIDE one old standard picture. Its labels are genuine designated
B-copies and physical A-support edge carriers, not arbitrary synthetic
copies or independent vertex/wagon incidence predicates.

At a fixed old train cut:
* vertices are the actual vertices of the partite picture;
* edge labels are physical A-support carrier SETS;
* designated labels remember their projected B-embedding;
* source edges of a designated copy are exactly those physical
  A-support carrier sets contained in its carrier;
* wagon labels are QUOTIENT classes of old support edges.

This realizes OrderOneData on the actual source geometry. In
particular, source-edge-to-designated-copy carrier compatibility
is definitional and cannot be silently violated.

Using the already checked active-boundary dichotomy, two distinct
vertices of a designated copy in the true active subsystem force
a genuine old A-support edge containing both. This discharges the
generic boundary-pair assumption of the four-occurrence theorem
for actual projected designated labels. It does not yet construct
the four-occurrence frame from the output picture step or transfer
system-girth along amalgamation.

No appendix is imported or validated.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X : Type v}

/-- The one-cut system-girth incidence record of a genuine old
partite picture: physical A-support edge labels, genuine projected
designated B-copies and genuine old train wagon quotient labels. -/
def standardPictureOrderOneData
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (μ : Fin (m + 1)) :
    OrderOneData X
      (OldACarrierEdge A C.toRelStructure)
      (DesignatedCopy B D C family)
      (Quotient (T.wagonSetoid μ)) where
  edgeCarrier := fun edge => edge.1
  copyCarrier := fun q => copyCarrier q.embedding
  copyEdges := fun q => {edge | edge.1 ⊆ copyCarrier q.embedding}
  parent := Quotient.mk (T.wagonSetoid μ)

/-- Every genuine physical A-support edge declared to belong to a
projected designated copy lies in that copy's vertex carrier by
construction. There is no additional coherence axiom. -/
theorem standardPictureOrderOneData_copyEdgeCarrierCompatible
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (μ : Fin (m + 1)) :
    (standardPictureOrderOneData A B D C family T μ).CopyEdgeCarrierCompatible := by
  intro q edge hEdge
  exact hEdge

/-- A projected designated old copy containing two distinct vertices
of the active subsystem supplies a PHYSICAL old A-support edge through
both. Its embedding as an actual A-subcopy is obtained from the
strong projected base image and active-boundary classification.

This is precisely the boundary hypothesis for
FourWagonFrame.pairEdge_of_system_bound_and_boundary in the genuine
old-standard model. -/
theorem standardPictureOrderOneData_pairEdge_of_two_active
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
    (q : DesignatedCopy B D C family)
    (x y : X) (hxy : x ≠ y)
    (hxCopy : x ∈ copyCarrier q.embedding)
    (hyCopy : y ∈ copyCarrier q.embedding)
    (hxActive : x ∈ activeCarrier A C e.toFunctionEmbedding)
    (hyActive : y ∈ activeCarrier A C e.toFunctionEmbedding) :
    (standardPictureOrderOneData A B D C family T μ).PairEdge x y := by
  rcases projectedCopy_activeCarrier_intersection_classify
      A B D C e q.base q.lift
      (hStrong q.base q.base_mem) with
    hSmall | ⟨aB, hEq⟩
  · exact False.elim
      (hxy (hSmall ⟨hxCopy, hxActive⟩ ⟨hyCopy, hyActive⟩))
  · let aOld : RelStructure.Embedding A C.toRelStructure :=
      q.embedding.comp aB
    let actualEdge : OldACarrierEdge A C.toRelStructure :=
      ⟨copyCarrier aOld, ⟨aOld, rfl⟩⟩
    have hxEdge : x ∈ actualEdge.1 := by
      change x ∈ copyCarrier aOld
      rw [← hEq]
      exact ⟨hxCopy, hxActive⟩
    have hyEdge : y ∈ actualEdge.1 := by
      change y ∈ copyCarrier aOld
      rw [← hEq]
      exact ⟨hyCopy, hyActive⟩
    exact ⟨actualEdge, hxEdge, hyEdge⟩

end StructuralRamsey.Girth
