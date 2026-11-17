import Girth.ActualDesignatedSupportBridge
import Girth.ForestPhysicalABCompletionExact
import Girth.ForestStructuralABCompletion

/-! # Finite sets of copies through an actual attachment -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}

/-- Preserve physical-copy completion in the actual partite attachment.
The support pieces added by the indexed assembly lift to genuine
transported designated copies. Every originally requested copy is retained. -/
theorem physicalCopySetForestExtension_actualAttachment
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (hB : B.Irreducible) [Finite VB]
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (Embedding B D)) (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hCover : DesignatedCoversIrreducibles B D C family)
    (hLocalCover : LocalIrreduciblesCoveredByAInCopies A E f)
    (hSourceNonempty : (supportCopies A (C.induce S).toRelStructure).Nonempty)
    (hSourceCover : ∀ s : S, ∃ e ∈ supportCopies A (C.induce S).toRelStructure, s ∈ e)
    (outer : I → StrongSupportEmbedding (supportCopies A (C.induce S).toRelStructure)
      (supportCopies A (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure))
    (hOuterCore : ∀ i (s : S), outer i s =
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f) (f i s))
    (m : ℕ) (hLocalForest : LocalForestThrough (fun i => (outer i).supportPiece) m)
    (hLinear : ALinear A (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure)
    (hOld : PhysicalCopySetForestExtension (pictureABPhysicalSupport A C.toRelStructure)
      (pictureABPhysicalEligible A B D C family) (pictureABPhysicalDesignated B D C family) m) :
    let New := StructuralRamsey.Partite.Attachment.attach C S E f
    PhysicalCopySetForestExtension (pictureABPhysicalSupport A New.toRelStructure)
      (pictureABPhysicalEligible A B D New family) (pictureABPhysicalDesignated B D New family) m := by
  let g := fun i => (f i).toEmbedding
  have hACover (a : Embedding A E.toRelStructure) : ∃ i, copyCarrier a ⊆ copyCarrier (g i) := by
    obtain ⟨i, a', hSub, hCopy⟩ := hLocalCover (copyCarrier a) (hA.range_embedding a)
    exact ⟨i, fun _ hx => hCopy (hSub ⟨_, hx⟩)⟩
  have hOldSupport := (pictureABPhysicalForestExtension_iff A B D C family m).mp hOld
  have hNewSupport := ForestCompletionProperty.assemble_actual_AB_from_local_copy_cover
    A hA C.toRelStructure S E.toRelStructure g hSourceNonempty hSourceCover outer hOuterCore m
    hLocalForest hLinear hACover (designatedPictureASupport A B D C family)
    (testedPictureABSupport A B D C family) hOldSupport
    (fun a => Or.inl ⟨a, rfl⟩) (fun _ => Or.inr)
  apply hNewSupport.toPhysicalCopySet
  · intro key hEligible
    cases key with
    | inl V =>
        obtain ⟨a, rfl⟩ := hEligible
        exact Or.inl ⟨a, rfl⟩
    | inr V =>
        obtain ⟨q, rfl⟩ := hEligible
        exact Or.inr (actualBCopy_mem_attachedDesignatedSupport
          A hA B hB D C family S E f hCover hLocalCover q.embedding)
  · rintro T ⟨i, R, ⟨q, rfl⟩, rfl⟩
    let transported := q.transportToStandard f i
    refine ⟨.inr (copyCarrier transported.embedding), ⟨transported, rfl⟩, ?_⟩
    exact (bSupportPiece_map_exact A q.embedding
      (StructuralRamsey.Partite.Attachment.copyEmbedding C S E f i).toEmbedding).symm

end StructuralRamsey.Girth
