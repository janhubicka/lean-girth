import Girth.ActivePicture
import Girth.IrreducibleAttachment
import Girth.AttachmentGeometry

/-! # Invariant package for one active picture step

The local-tree construction repeatedly performs the same operation: replace the
true active subsystem by a local Ramsey witness and freely attach fresh copies
of the old picture.  The component lemmas are already formalized; this module
packages exactly the invariants consumed by the manuscript's preservation
proposition.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- One active picture step preserves both projection-level and actual
irreducible coverage, and exposes the exact free-attachment intersections of
the standard copies. -/
theorem activePictureStep_invariants
    (A : RelStructure L UA)
    (B₀ : RelStructure L VB)
    (D₀ : RelStructure L P)
    (C₀ : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C₀.induce (activeCarrier A C₀ α)) E)
    (κ : Type*)
    (hPartite : C₀.IsPartiteOver D₀)
    (hCover :
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy C₀ B₀ D₀)
    (hActualC :
      RelStructure.IrreduciblesExtendTo B₀ C₀.toRelStructure)
    (hEPartite : E.IsPartiteOver D₀)
    (hECover :
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy E B₀ D₀)
    (hActualE :
      RelStructure.IrreduciblesExtendTo B₀ E.toRelStructure)
    (hLocal :
      ∀ χ :
          StructuralRamsey.Partite.ProjectedEmbedding A E α → κ,
        ∃ i : I,
          ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A C₀ α,
            χ ((activeInduceProjected A e₁
              (projected_mem_activeCarrier A C₀ α e₁)).comp (f i)) =
              χ ((activeInduceProjected A e₂
                (projected_mem_activeCarrier A C₀ α e₂)).comp (f i))) :
    let S := activeCarrier A C₀ α
    let C₁ := StructuralRamsey.Partite.Attachment.attach C₀ S E f
    C₁.IsPartiteOver D₀ ∧
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy C₁ B₀ D₀ ∧
      RelStructure.IrreduciblesExtendTo B₀ C₁.toRelStructure ∧
      StructuralRamsey.Partite.PictureProperty A C₀ α C₁ κ ∧
      (∀ i : I,
        copyCarrier
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C₀ S E f i).toEmbedding ∩
          copyCarrier
            (StructuralRamsey.Partite.Attachment.coreEmbedding
              C₀ S E f).toEmbedding =
        copyCarrier
          ((StructuralRamsey.Partite.Attachment.coreEmbedding
              C₀ S E f).toEmbedding.comp
            ((f i).toEmbedding))) ∧
      (∀ ⦃i j : I⦄, i ≠ j →
        copyCarrier
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C₀ S E f i).toEmbedding ∩
          copyCarrier
            (StructuralRamsey.Partite.Attachment.copyEmbedding
              C₀ S E f j).toEmbedding ⊆
        copyCarrier
            (StructuralRamsey.Partite.Attachment.coreEmbedding
              C₀ S E f).toEmbedding) := by
  classical
  let S := activeCarrier A C₀ α
  let C₁ := StructuralRamsey.Partite.Attachment.attach C₀ S E f
  have hStep :=
    activeInducedPictureStep_onActiveCarrier
      A B₀ D₀ C₀ α E f κ
      hPartite hCover hEPartite hECover hLocal
  have hActual :
      RelStructure.IrreduciblesExtendTo B₀ C₁.toRelStructure := by
    exact irreduciblesExtendTo_partiteAttachment
      B₀ C₀ S E f hActualC hActualE
  refine ⟨hStep.1, hStep.2.1, hActual, hStep.2.2, ?_, ?_⟩
  · intro i
    exact attachment_copy_core_intersection
      C₀.toRelStructure S E.toRelStructure
      (fun k => (f k).toEmbedding) i
  · intro i j hij
    exact attachment_copy_copy_intersection_subset_core
      C₀.toRelStructure S E.toRelStructure
      (fun k => (f k).toEmbedding) hij

end StructuralRamsey.Girth
