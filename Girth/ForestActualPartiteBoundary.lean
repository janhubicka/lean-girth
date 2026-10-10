import Girth.ForestCoreFactorBoundary
import Girth.ActiveBoundary

/-!
# Actual projected B-copy boundary is a complete local A-support edge

The abstract direct forest increment uses SmallOrWholeEdgeBoundary,
with two important support-edge membership requirements.

For a genuine projected B-copy in the standard partite attachment,
the checked ActiveBoundary lemma classifies its overlap with the
local core as subsingleton or the carrier of a transported A-subcopy.
The general mapped-core factorization theorem now certifies both
membership in the selected B-piece's complete A-support AND in the
actual mapped A-support hypergraph of the local core.

This is not a mere carrier-containment statement.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Actual strong projected B-copy boundary satisfies the EXACT
small-or-whole-edge support condition against the mapped local
A-support of its attached core. -/
theorem attachedProjectedBCopy_smallOrWholeBoundary
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
    (i : I) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    SmallOrWholeEdgeBoundary
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier (core.comp aE)}
      (copyCarrier core)
      (embeddedACopySupportPiece A (copyI.comp q.val)) := by
  let S := activeCarrier A C e.toFunctionEmbedding
  let copyI :=
    (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  have hBoundary :
      (copyCarrier (copyI.comp q.val) ∩ copyCarrier core).Subsingleton ∨
        ∃ aB : RelStructure.Embedding A B,
          copyCarrier (copyI.comp q.val) ∩ copyCarrier core =
            copyCarrier ((copyI.comp q.val).comp aB) := by
    rcases
        attachedProjectedCopy_core_intersection_classify
          A B D C e b q hStrong E f i with
      hs | ⟨aB, hEq⟩
    · exact Or.inl hs
    · right
      refine ⟨aB, ?_⟩
      simpa only [RelStructure.Embedding.comp_assoc] using hEq
  exact embeddedACopySupportPiece_boundary_of_core
    A core (copyI.comp q.val) hBoundary


/-- Actual projected A-copy version: base A-linearity supplies the
strongness of its projected image automatically. Thus selected
ambient A-edge members satisfy the same precise local boundary
condition as selected B copies. -/
theorem attachedProjectedACopy_smallOrWholeBoundary
    (A : RelStructure L UA)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (e b : RelStructure.Embedding A D)
    (q : StructuralRamsey.Partite.ProjectedEmbedding A C b)
    (hLinear : ALinear A D)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (i : I) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let copyI :=
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
    let core :=
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
    SmallOrWholeEdgeBoundary
      {t : Set (StructuralRamsey.Partite.Attachment.Vertex S
          (W := Y) (I := I)) |
        ∃ aE : RelStructure.Embedding A E.toRelStructure,
          t = copyCarrier (core.comp aE)}
      (copyCarrier core)
      (embeddedACopySupportPiece A (copyI.comp q.val)) :=
  attachedProjectedBCopy_smallOrWholeBoundary
    A A D C e b q (aStrong_copyCarrier_of_aLinear hLinear b)
    E f i

end StructuralRamsey.Girth
