import Girth.TrainCoreCopyVertexCoverage
import Girth.TrainActualCopyLocalCoreIncidence

set_option Elab.async false

/-!
# The active shared witness is the literal whole-gluing-image system

The generated-train machinery describes a gluing copy by the union of its
genuine shared A-support edges.  The local induction describes that copy
by the complete image of its embedding.  For the true active subsystem
these are exactly the same incidence data, including source-edge ownership.

Every core A-edge contained in a gluing image pulls back through the
embedding to a genuine shared old A-edge.  This uses induced embedding
reflection, with no strongness or finiteness assumption.  Pointwise active
support coverage separately identifies the whole vertex carrier.  All
physical core edges, quotient wagon labels, and prescribed indices remain
literal; equal images are not deduplicated.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- A physical core A-edge belongs to the canonical shared-edge image
exactly when its entire carrier is contained in the prescribed gluing
copy.  No active-support, irreducibility or strongness premise is needed. -/
theorem sharedOldACarrierCoreEmbedding_mem_range_iff
    {L : RelLanguage.{u}} {UA X Y I : Type v}
    (A : RelStructure L UA) (B : RelStructure L X) (S : Set X)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding (B.induce S) R)
    (i : I) (edge : OldACarrierEdge A R) :
    edge ∈ Set.range (sharedOldACarrierCoreEmbedding A B S R f i) ↔
      edge.1 ⊆ copyCarrier (f i) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact sharedOldACarrierCoreEmbedding_carrier_subset_local_copy A B S R f i s
  · intro hSub
    classical
    obtain ⟨a, ha⟩ := edge.2
    have hRange : ∀ u : UA, ∃ x : S, a u = f i x := by
      intro u
      have hu : a u ∈ edge.1 := by
        rw [ha]
        exact ⟨u, rfl⟩
      obtain ⟨x, hx⟩ := hSub hu
      exact ⟨x, hx.symm⟩
    let aS := a.factorThroughRange (f i) hRange
    let old := (B.inclusion S).comp aS
    have hOldSub : copyCarrier old ⊆ S := by
      rintro x ⟨u, rfl⟩
      exact (aS u).2
    let s : SharedOldACarrierEdge A B S :=
      ⟨⟨copyCarrier old, ⟨old, rfl⟩⟩, hOldSub⟩
    let core := RelStructure.Attachment.coreEmbedding B S R f
    let std := RelStructure.Attachment.copyEmbedding B S R f i
    have hMaps : std.comp old = core.comp a := by
      apply RelStructure.Embedding.ext
      intro u
      calc
        std (old u) = core (f i (aS u)) :=
          RelStructure.Attachment.copy_extends B S R f i (aS u)
        _ = core (a u) :=
          congrArg core (Classical.choose_spec (hRange u)).symm
    have hImages :
        (fun y : Y => core y) ''
            (sharedOldACarrierCoreEmbedding A B S R f i s).1 =
          (fun y : Y => core y) '' edge.1 := by
      calc
        _ = (fun x : X => std x) '' copyCarrier old :=
          (sharedOldACarrierCoreMap_image A B S R f i s).symm
        _ = copyCarrier (std.comp old) :=
          (copyCarrier_comp_eq_image std old).symm
        _ = copyCarrier (core.comp a) := congrArg copyCarrier hMaps
        _ = (fun y : Y => core y) '' copyCarrier a :=
          copyCarrier_comp_eq_image core a
        _ = (fun y : Y => core y) '' edge.1 := by rw [ha]
    refine ⟨s, Subtype.ext ?_⟩
    exact supportCarrier_image_eq_of_injective core core.injective hImages

/-- The true active subsystem has no unsupported gluing vertices, so the
shared-witness designated carrier is exactly the entire gluing-copy image. -/
theorem activeCoreWitness_copyCarrier_eq
    {L : RelLanguage.{u}} {UA P X Y I : Type v}
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) (i : I) :
    (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure (activeCarrier A C α) R f)
      (fun edge : OldACarrierEdge A R => edge.1)).copyCarrier i =
      copyCarrier (f i) := by
  ext y
  constructor
  · rintro ⟨s, hy⟩
    exact sharedOldACarrierCoreEmbedding_carrier_subset_local_copy
      A C.toRelStructure (activeCarrier A C α) R f i s hy
  · intro hy
    exact activeCoreWitness_vertex_mem_sharedCopy A C α R f U μ i y hy

/-- The literal local system uses whole gluing-copy images and all ambient
physical A-edges; belonging to a designated copy means whole-edge
containment.  The prescribed copy index is retained even for equal images. -/
def activeGluingWitnessOrderOneData
    {L : RelLanguage.{u}} {UA P X Y I : Type v}
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) :
    OrderOneData Y (OldACarrierEdge A R) I (Quotient (U.wagonSetoid μ)) where
  edgeCarrier := fun edge => edge.1
  copyCarrier := fun i => copyCarrier (f i)
  copyEdges := fun i => {edge | edge.1 ⊆ copyCarrier (f i)}
  parent := Quotient.mk (U.wagonSetoid μ)

/-- The whole-image local system and the shared-support local system are
equal as complete incidence records, with the same actual edge, designated
and wagon labels.  Hence their full system-girth predicates agree literally. -/
theorem activeGluingWitnessOrderOneData_eq_shared
    {L : RelLanguage.{u}} {UA P X Y I : Type v}
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m : ℕ} (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (μ : Fin (m + 1)) :
    activeGluingWitnessOrderOneData A C α R f U μ =
      sharedWitnessOrderOneData U μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure (activeCarrier A C α) R f)
        (fun edge : OldACarrierEdge A R => edge.1) := by
  have hCarrier : (fun i => copyCarrier (f i)) =
      (sharedWitnessOrderOneData U μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure (activeCarrier A C α) R f)
        (fun edge : OldACarrierEdge A R => edge.1)).copyCarrier := by
    funext i
    exact (activeCoreWitness_copyCarrier_eq A C α R f U μ i).symm
  have hEdges : (fun i => {edge : OldACarrierEdge A R | edge.1 ⊆ copyCarrier (f i)}) =
      (fun i => Set.range
        (sharedOldACarrierCoreEmbedding A C.toRelStructure (activeCarrier A C α) R f i)) := by
    funext i
    ext edge
    exact (sharedOldACarrierCoreEmbedding_mem_range_iff
      A C.toRelStructure (activeCarrier A C α) R f i edge).symm
  unfold activeGluingWitnessOrderOneData sharedWitnessOrderOneData
  change (fun i => copyCarrier (f i)) = _ at hCarrier
  rw [hCarrier, hEdges]
  rfl

end StructuralRamsey.Girth
