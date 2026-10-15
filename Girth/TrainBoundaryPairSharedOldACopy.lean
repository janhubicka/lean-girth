import Girth.TrainBoundaryPairCoreSupport

/-!
# Circulation: keep the OLD A-copy at a two-point boundary intersection

For the unrestricted two-standard argument, the active-boundary
dichotomy must produce an actual A-support copy inside the ORIGINAL
designated old standard picture, not merely an A-copy in the witness
core. The existing dichotomy already gives exactly this sharper
conclusion: if a projected B-copy has two distinct vertices in the
gluing core, its intersection with the core is the whole image of a
genuine A-subcopy of B.

This theorem records the original A-subcopy AND its entire physical
carrier contained in the core. The two given boundary vertices lie
in that copy. No finiteness, surjectivity of A self-embeddings,
generated output-wagon linearity or appendix result is required.

The later use is to show a source designated label containing both
boundary vertices contains a true old physical A-edge through them.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Two distinct boundary points of a genuine projected B-copy in the
core force an ORIGINAL old A-subcopy of B covering the pair.
Its whole attached physical carrier lies inside the local core. -/
theorem attachedProjectedCopy_two_core_vertices_have_sharedOldACopy
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A D)
    (b : RelStructure.Embedding B D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding B C b)
    (hStrong : AStrong A D (copyCarrier b))
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (i : I)
    (x y : RelStructure.Attachment.Vertex
      (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I))
    (hxy : x ≠ y) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    x ∈ copyCarrier (copyI.comp q.val) →
    y ∈ copyCarrier (copyI.comp q.val) →
    x ∈ copyCarrier core →
    y ∈ copyCarrier core →
    ∃ aB : RelStructure.Embedding A B,
      x ∈ copyCarrier (copyI.comp (q.val.comp aB)) ∧
      y ∈ copyCarrier (copyI.comp (q.val.comp aB)) ∧
      copyCarrier (copyI.comp (q.val.comp aB)) ⊆
        copyCarrier core := by
  dsimp only
  intro hxCopy hyCopy hxCore hyCore
  rcases attachedProjectedCopy_core_intersection_classify
      A B D C e b q hStrong E f i with
    hSmall | ⟨aB, hEq⟩
  · exact False.elim
      (hxy (hSmall ⟨hxCopy, hxCore⟩ ⟨hyCopy, hyCore⟩))
  · refine ⟨aB, ?_, ?_, ?_⟩
    · rw [← hEq]
      exact ⟨hxCopy, hxCore⟩
    · rw [← hEq]
      exact ⟨hyCopy, hyCore⟩
    · rw [← hEq]
      exact Set.inter_subset_right

end StructuralRamsey.Girth
