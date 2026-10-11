import Girth.LocalForestPieces
import Girth.ActivePicture

/-!
# Actual small gluing support is exactly the attached core image

The conditional free-picture forest theorem still takes an
identification of a small gluing support piece with the image of
its gluing copy inside the new core.

In a genuine partite picture step, this is NOT extra combinatorial
information. If the source strong support embedding has the SAME
image as the whole true active subsystem, and its vertex map factors
through the standard attached copy, the free attachment identity
copy_extends shows that its support carrier is exactly the core
image of the source under the corresponding local f_i embedding.

This is a pure geometry theorem: no edge Ramsey property, girth,
finite forest or coverage normalization is assumed. It explicitly
requires surjectivity onto the TRUE active carrier, not the larger
union of all vertices in selected base parts.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y Src I : Type v}

/-- The strong gluing support of a genuinely complete source copy
has precisely the core image carrier. -/
theorem actualSmallGluing_supportCarrier_eq_coreCopy
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (e : RelStructure.Embedding A (RelStructure L P))
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    {H : Set (Set Src)}
    {K : Set (Set (StructuralRamsey.Partite.Attachment.Vertex
       (activeCarrier A C e.toFunctionEmbedding)
       (W := Y) (I := I)))}
    (outer : I → StrongSupportEmbedding H K)
    (active : I → Src ↪ X)
    (hFactor : ∀ i x, outer i x =
      (StructuralRamsey.Partite.Attachment.copyEmbedding C
        (activeCarrier A C e.toFunctionEmbedding) E f i).toEmbedding
        (active i x))
    (hActiveRange : ∀ i,
      Set.range (active i) = activeCarrier A C e.toFunctionEmbedding)
    (i : I) :
    (outer i).supportPiece.carrier =
      copyCarrier
        (((StructuralRamsey.Partite.Attachment.coreEmbedding C
          (activeCarrier A C e.toFunctionEmbedding) E f).toEmbedding).comp
          (f i).toEmbedding) := by
  classical
  let S := activeCarrier A C e.toFunctionEmbedding
  let core :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  change Set.range (outer i) = Set.range (core.comp (f i).toEmbedding)
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have hxin : active i x ∈ S := by
      rw [← hActiveRange i]
      exact ⟨x, rfl⟩
    let y : S := ⟨active i x, hxin⟩
    refine ⟨y, ?_⟩
    change outer i x = core (f i y)
    calc
      outer i x =
        (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
          (active i x) := hFactor i x
      _ = core (f i y) :=
        StructuralRamsey.Partite.Attachment.copy_extends C S E f i y
  · rintro ⟨y, rfl⟩
    have hyin : y.val ∈ Set.range (active i) := by
      rw [hActiveRange i]
      exact y.property
    obtain ⟨x, hxy⟩ := hyin
    refine ⟨x, ?_⟩
    change outer i x = core (f i y)
    calc
      outer i x =
        (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
          (active i x) := hFactor i x
      _ = (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding
          y.val := congrArg
            (fun z : X =>
              (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding z)
            hxy
      _ = core (f i y) :=
        StructuralRamsey.Partite.Attachment.copy_extends C S E f i y

end StructuralRamsey.Girth
