import Girth.PictureProjectionGeometry

/-! # Standard-copy owners for untouched projected copies

In a free picture attachment, every irreducible copy lies in the core or in
one standard copy.  For an untouched A-fibre the core alternative is
impossible as soon as the active and untouched base supports have
subsingleton intersection.  This packages the owner assignment used by the
circulation girth-preservation argument.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- An irreducible ambient copy which is not contained in the core has a
standard-copy owner. -/
theorem irreducibleEmbedding_has_standard_owner_of_not_core
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (hA : A.Irreducible)
    (a : RelStructure.Embedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure)
    (hNotCore :
      ¬ copyCarrier a ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.coreEmbedding
            C S E f).toEmbedding) :
    ∃ i : I,
      copyCarrier a ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            C S E f i).toEmbedding := by
  classical
  let Whole :=
    (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure
  let T : Set (StructuralRamsey.Partite.Attachment.Vertex
      S (W := Y) (I := I)) :=
    copyCarrier a
  have hT : (Whole.induce T).Irreducible :=
    hA.range_embedding a
  rcases
      RelStructure.Attachment.irreducible_core_or_copy
        (B := C.toRelStructure) (S := S) (D := E.toRelStructure)
        (f := fun i => (f i).toEmbedding) T hT with
    hCore | ⟨i, hCopy⟩
  · exfalso
    apply hNotCore
    intro z hz
    let zT : T := ⟨z, hz⟩
    rcases hCore zT with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change
      Sum.inl y = z
    exact hy.symm
  · refine ⟨i, ?_⟩
    intro z hz
    let zT : T := ⟨z, hz⟩
    rcases hCopy zT with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change
      RelStructure.Attachment.copyMap
        C.toRelStructure S E.toRelStructure
        (fun k => (f k).toEmbedding) i x = z
    exact hx.symm

/-- A projected A-copy over beta cannot lie in a core whose parts all lie over
alpha when the two base supports meet in at most one part and A has two
specified distinct vertices. -/
theorem projectedCopy_not_subset_core_of_subsingleton_base_intersection
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (u v : UA) (huv : u ≠ v) :
    ¬ copyCarrier a.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.coreEmbedding
            C S E f).toEmbedding := by
  classical
  intro hSub
  have huCore :=
    hSub (show a.val u ∈ copyCarrier a.val from ⟨u, rfl⟩)
  have hvCore :=
    hSub (show a.val v ∈ copyCarrier a.val from ⟨v, rfl⟩)
  rcases huCore with ⟨yu, hyu⟩
  rcases hvCore with ⟨yv, hyv⟩
  have huPart : E.part yu = β u := by
    calc
      E.part yu =
          (StructuralRamsey.Partite.Attachment.attach C S E f).part
            ((StructuralRamsey.Partite.Attachment.coreEmbedding
              C S E f) yu) :=
        ((StructuralRamsey.Partite.Attachment.coreEmbedding
          C S E f).map_part yu).symm
      _ =
          (StructuralRamsey.Partite.Attachment.attach C S E f).part
            (a.val u) := congrArg
              (StructuralRamsey.Partite.Attachment.attach C S E f).part hyu
      _ = β u := a.property u
  have hvPart : E.part yv = β v := by
    calc
      E.part yv =
          (StructuralRamsey.Partite.Attachment.attach C S E f).part
            ((StructuralRamsey.Partite.Attachment.coreEmbedding
              C S E f) yv) :=
        ((StructuralRamsey.Partite.Attachment.coreEmbedding
          C S E f).map_part yv).symm
      _ =
          (StructuralRamsey.Partite.Attachment.attach C S E f).part
            (a.val v) := congrArg
              (StructuralRamsey.Partite.Attachment.attach C S E f).part hyv
      _ = β v := a.property v
  have huI : β u ∈ Set.range α ∩ Set.range β := by
    constructor
    · rw [← huPart]
      exact hCoreSupport yu
    · exact ⟨u, rfl⟩
  have hvI : β v ∈ Set.range α ∩ Set.range β := by
    constructor
    · rw [← hvPart]
      exact hCoreSupport yv
    · exact ⟨v, rfl⟩
  have hβ : β u = β v := hInter huI hvI
  exact huv (β.injective hβ)

/-- Consequently an untouched projected irreducible A-copy has a standard
owner. -/
theorem projectedCopy_has_standard_owner_of_subsingleton_base_intersection
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (α β : UA ↪ P)
    (hA : A.Irreducible)
    (hCoreSupport : ∀ y : Y, E.part y ∈ Set.range α)
    (hInter : (Set.range α ∩ Set.range β).Subsingleton)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C S E f) β)
    (u v : UA) (huv : u ≠ v) :
    ∃ i : I,
      copyCarrier a.val ⊆
        copyCarrier
          (StructuralRamsey.Partite.Attachment.copyEmbedding
            C S E f i).toEmbedding :=
  irreducibleEmbedding_has_standard_owner_of_not_core
    A C S E f hA a.val
      (projectedCopy_not_subset_core_of_subsingleton_base_intersection
        A C S E f α β hCoreSupport hInter a u v huv)

end StructuralRamsey.Girth
