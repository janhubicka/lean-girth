import Girth.UntouchedOwner
import Girth.AttachmentGeometry

/-! # Owner changes for untouched projected copies

For each A-copy in an untouched fibre, choose one standard picture containing
it. At a change of owner, a shared connector lies in the core and in both
corresponding gluing-copy images. This is exactly the picture-specific input
needed by cyclic owner-run compression.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Chosen standard-copy owner of an untouched projected A-copy. -/
noncomputable def untouchedOwner
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β) :
    I :=
  Classical.choose
    (projectedCopy_has_standard_owner_of_subsingleton_base_intersection
      A C S E f α β hA hCoreSupport hInter a u v huv)

/-- The chosen owner contains the whole projected A-copy. -/
theorem untouchedOwner_spec
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β) :
    copyCarrier a.val ⊆
      copyCarrier
        (StructuralRamsey.Partite.Attachment.copyEmbedding
          C S E f
          (untouchedOwner A C S E f α β hA hCoreSupport
            hInter u v huv a)).toEmbedding :=
  Classical.choose_spec
    (projectedCopy_has_standard_owner_of_subsingleton_base_intersection
      A C S E f α β hA hCoreSupport hInter a u v huv)

/-- At a genuine owner change, a shared point of the two untouched A-copies
has one core representative lying in both local gluing-copy images. -/
theorem untouchedOwner_change_shared_point
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (z : StructuralRamsey.Partite.Attachment.Vertex
      S (W := Y) (I := I))
    (hzA : z ∈ copyCarrier a.val)
    (hzB : z ∈ copyCarrier b.val)
    (hOwner :
      untouchedOwner A C S E f α β hA hCoreSupport
          hInter u v huv a ≠
        untouchedOwner A C S E f α β hA hCoreSupport
          hInter u v huv b) :
    ∃ y : Y,
      (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f) y = z ∧
      y ∈ copyCarrier
        ((f (untouchedOwner A C S E f α β hA hCoreSupport
          hInter u v huv a)).toEmbedding) ∧
      y ∈ copyCarrier
        ((f (untouchedOwner A C S E f α β hA hCoreSupport
          hInter u v huv b)).toEmbedding) := by
  let ia :=
    untouchedOwner A C S E f α β hA hCoreSupport
      hInter u v huv a
  let ib :=
    untouchedOwner A C S E f α β hA hCoreSupport
      hInter u v huv b
  have hzI :
      z ∈ copyCarrier
        (StructuralRamsey.Partite.Attachment.copyEmbedding
          C S E f ia).toEmbedding :=
    untouchedOwner_spec
      A C S E f α β hA hCoreSupport hInter u v huv a hzA
  have hzJ :
      z ∈ copyCarrier
        (StructuralRamsey.Partite.Attachment.copyEmbedding
          C S E f ib).toEmbedding :=
    untouchedOwner_spec
      A C S E f α β hA hCoreSupport hInter u v huv b hzB
  have hIJ : ia ≠ ib := by
    simpa [ia, ib] using hOwner
  obtain ⟨y, hy, hyI, hyJ⟩ :=
    attachment_shared_point_in_both_local_images
      C.toRelStructure S E.toRelStructure
      (fun k => (f k).toEmbedding)
      hIJ hzI hzJ
  refine ⟨y, ?_, ?_, ?_⟩
  · change Sum.inl y = z
    change Sum.inl y = z at hy
    exact hy
  · simpa [ia] using hyI
  · simpa [ib] using hyJ

/-- The same owner-change statement as membership in the core images of the
two gluing copies. -/
theorem untouchedOwner_change_shared_point_mapped
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (u v : UA) (huv : u ≠ v)
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (z : StructuralRamsey.Partite.Attachment.Vertex
      S (W := Y) (I := I))
    (hzA : z ∈ copyCarrier a.val)
    (hzB : z ∈ copyCarrier b.val)
    (hOwner :
      untouchedOwner A C S E f α β hA hCoreSupport
          hInter u v huv a ≠
        untouchedOwner A C S E f α β hA hCoreSupport
          hInter u v huv b) :
    z ∈
        (StructuralRamsey.Partite.Attachment.coreEmbedding
          C S E f) ''
          copyCarrier
            ((f (untouchedOwner A C S E f α β hA hCoreSupport
              hInter u v huv a)).toEmbedding) ∧
      z ∈
        (StructuralRamsey.Partite.Attachment.coreEmbedding
          C S E f) ''
          copyCarrier
            ((f (untouchedOwner A C S E f α β hA hCoreSupport
              hInter u v huv b)).toEmbedding) := by
  obtain ⟨y, hy, hyA, hyB⟩ :=
    untouchedOwner_change_shared_point
      A C S E f α β hA hCoreSupport hInter u v huv
      a b z hzA hzB hOwner
  constructor
  · exact ⟨y, hyA, hy⟩
  · exact ⟨y, hyB, hy⟩

end StructuralRamsey.Girth
