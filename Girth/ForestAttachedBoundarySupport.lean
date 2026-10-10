import Girth.ActiveBoundary
import Girth.ForestDistinctBoundaryAllowed

/-!
# Actual relational boundary classification implies support-piece boundary

The partite free attachment already classifies the intersection of
an attached projected B-copy with the local core as subsingleton or
the *whole carrier* of one attached A-subcopy.

The forest increment needs a slightly stronger conclusion: that
A-carrier is both a local core support edge and an edge of the
selected B-support PIECE. The two necessary support-membership
facts are kept explicit below instead of incorrectly deducing them
from carrier inclusion alone.

Thus this lemma is a precise, circulation-facing geometric interface
between ActiveBoundary and SmallOrWholeEdgeBoundary; it does not
construct a Ramsey witness.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Upgrade the actual projected B-copy/core intersection dichotomy
to the exact hypergraph-support boundary criterion, assuming that
the projected A-subcopies are genuine edges of the selected support
and that those lying wholly in the core belong to the local support. -/
theorem attachedProjectedCopy_smallOrWholeSupportBoundary
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
    (F : HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I)))
    (K : Set (Set
      (StructuralRamsey.Partite.Attachment.Vertex
        (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I))))
    (hCarrier :
      F.carrier =
        copyCarrier
          (((StructuralRamsey.Partite.Attachment.copyEmbedding
            C (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding).comp q.val))
    (hOwnEdges : ∀ aB : RelStructure.Embedding A B,
      copyCarrier
        (((StructuralRamsey.Partite.Attachment.copyEmbedding
          C (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding).comp
          (q.val.comp aB)) ∈ F.edges)
    (hCoreEdges : ∀ aB : RelStructure.Embedding A B,
      copyCarrier
        (((StructuralRamsey.Partite.Attachment.copyEmbedding
          C (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding).comp
          (q.val.comp aB)) ⊆
            copyCarrier ((StructuralRamsey.Partite.Attachment.coreEmbedding
              C (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding) →
      copyCarrier
        (((StructuralRamsey.Partite.Attachment.copyEmbedding
          C (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding).comp
          (q.val.comp aB)) ∈ K) :
    SmallOrWholeEdgeBoundary K
      (copyCarrier ((StructuralRamsey.Partite.Attachment.coreEmbedding
        C (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding))
      F := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let copyI :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  have hGeom :
      (copyCarrier (copyI.comp q.val) ∩ copyCarrier core).Subsingleton ∨
        ∃ aB : RelStructure.Embedding A B,
          copyCarrier (copyI.comp q.val) ∩ copyCarrier core =
            copyCarrier (copyI.comp (q.val.comp aB)) :=
    attachedProjectedCopy_core_intersection_classify
      A B D C e b q hStrong E f i
  rcases hGeom with hSmall | ⟨aB, hEq⟩
  · left
    rw [hCarrier]
    exact hSmall
  · right
    let ed : Set _ := copyCarrier (copyI.comp (q.val.comp aB))
    have hedSub : ed ⊆ copyCarrier core := by
      intro x hx
      have hxPair :
          x ∈ copyCarrier (copyI.comp q.val) ∩ copyCarrier core := by
        rw [hEq]
        exact hx
      exact hxPair.2
    refine ⟨ed, hCoreEdges aB hedSub, hOwnEdges aB, ?_⟩
    rw [hCarrier]
    exact hEq

end StructuralRamsey.Girth
