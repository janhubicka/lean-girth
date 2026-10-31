import Girth.TrainSelectedPictureCorePairGeometry
import Girth.TrainActualPhysicalEdgeCarrierEval

/-!
# No new physical pair edge between distinct core vertices

A genuine ambient A-support edge meeting an A-strong core in two
distinct vertices must be wholly contained in that core; the checked
physical-core edge pullback recovers the original core support edge.
Thus the attachment CANNOT introduce a new physical pair edge
between two embedded core vertices.

This is the missing contrapositive to transport the physical nonedge
condition of a reduced witness LongValid piece to the actual output.
It uses A-strongness of the old active gluing subsystem explicitly;
mere inducedness is insufficient. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA Old Core I : Type v}

/-- For two different core vertices, any actual support-edge pair
in the attached relational picture reflects to a genuine core edge.
No output linearity, witness girth or set of designated copies is
assumed. The exact A-strong active-subsystem premise is visible. -/
theorem attachment_core_pairEdge_back_of_aStrong
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L Old) (S : Set Old)
    (R : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) R)
    (hActive : AStrong A B S)
    (x y : Core) (hxy : x ≠ y)
    (hPair : ∃ g : OldACarrierEdge A
        (RelStructure.Attachment.attach B S R f),
      (RelStructure.Attachment.coreEmbedding B S R f) x ∈ g.1 ∧
      (RelStructure.Attachment.coreEmbedding B S R f) y ∈ g.1) :
    ∃ b : OldACarrierEdge A R, x ∈ b.1 ∧ y ∈ b.1 := by
  let CoreEmb := RelStructure.Attachment.coreEmbedding B S R f
  let Actual := RelStructure.Attachment.attach B S R f
  let CoreActual (b : OldACarrierEdge A R) :=
    actualAPictureEdgeEquiv A hA B S R f
      (physicalCoreEdge (sharedOldACarrierInclusion A B S) I b)
  obtain ⟨g, hx, hy⟩ := hPair
  have hStrong : AStrong A Actual (copyCarrier CoreEmb) :=
    attachment_core_aStrong B S R f hA hActive
  have hXY : CoreEmb x ≠ CoreEmb y := by
    intro heq
    exact hxy (CoreEmb.injective heq)
  have hXCore : CoreEmb x ∈ copyCarrier CoreEmb := ⟨x, rfl⟩
  have hYCore : CoreEmb y ∈ copyCarrier CoreEmb := ⟨y, rfl⟩
  have hSub : g.1 ⊆ copyCarrier CoreEmb :=
    oldACarrier_subset_of_two_mem_aStrong A Actual
      (copyCarrier CoreEmb) hStrong g (CoreEmb x) (CoreEmb y)
      hXY hx hy hXCore hYCore
  obtain ⟨b, hb⟩ :=
    actualASupport_core_edge_pullback A hA B S R f g hSub
  have hEdgeEq : CoreActual b = g := hb
  have hxImage : CoreEmb x ∈ attachedCoreAEdgeCarrier A B S R f b := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f b]
    change CoreEmb x ∈ (CoreActual b).1
    exact (congrArg
      (fun z : OldACarrierEdge A Actual => CoreEmb x ∈ z.1)
      hEdgeEq).symm.mp hx
  have hyImage : CoreEmb y ∈ attachedCoreAEdgeCarrier A B S R f b := by
    rw [← actualAPictureEdgeEquiv_core_carrier A hA B S R f b]
    change CoreEmb y ∈ (CoreActual b).1
    exact (congrArg
      (fun z : OldACarrierEdge A Actual => CoreEmb y ∈ z.1)
      hEdgeEq).symm.mp hy
  have hxCore : x ∈ b.1 := by
    change CoreEmb x ∈ (fun t : Core => CoreEmb t) '' b.1 at hxImage
    obtain ⟨t, ht, htx⟩ := hxImage
    have hEq : t = x := CoreEmb.injective htx
    simpa [hEq] using ht
  have hyCore : y ∈ b.1 := by
    change CoreEmb y ∈ (fun t : Core => CoreEmb t) '' b.1 at hyImage
    obtain ⟨t, ht, hty⟩ := hyImage
    have hEq : t = y := CoreEmb.injective hty
    simpa [hEq] using ht
  exact ⟨b, hxCore, hyCore⟩

/-- In contrapositive form, a core pair not joined by any genuine
core support edge remains a physical nonedge after attachment.
This is precisely the nonedge condition required for a new long
replacement of the original selected-picture cycle. -/
theorem attachment_core_nonpair_preserved_of_aStrong
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L Old) (S : Set Old)
    (R : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) R)
    (hActive : AStrong A B S)
    (x y : Core) (hxy : x ≠ y)
    (hNoPair : ¬ ∃ b : OldACarrierEdge A R,
      x ∈ b.1 ∧ y ∈ b.1) :
    ¬ ∃ g : OldACarrierEdge A
        (RelStructure.Attachment.attach B S R f),
      (RelStructure.Attachment.coreEmbedding B S R f) x ∈ g.1 ∧
      (RelStructure.Attachment.coreEmbedding B S R f) y ∈ g.1 := by
  intro hPair
  exact hNoPair
    (attachment_core_pairEdge_back_of_aStrong
      A hA B S R f hActive x y hxy hPair)

end StructuralRamsey.Girth
