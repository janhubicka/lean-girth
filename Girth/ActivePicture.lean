import PartiteConstruction.Partite.InducedStep

/-! # Picture steps over the true active subsystem

The generic `Picture.build` in `partite-construction` attaches along every
vertex whose part lies in the selected set of parts.  The girth manuscript uses
a smaller subsystem: only vertices lying in an A-copy with the prescribed
projection are active.  Boundary vertices belonging to those parts but to no
such A-copy must remain private.

This file isolates the exact free-attachment shell needed for that version.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- The true active vertex set for a projection alpha: precisely the union
of the carriers of A-copies with that projection.  This is the manuscript's
vertex set of P[e]. -/
def activeCarrier
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P X)
    (α : UA → P) : Set X :=
  {x | ∃ e : StructuralRamsey.Partite.ProjectedEmbedding A B α,
    x ∈ Set.range e.val}

/-- Every projected A-copy lies pointwise in the active carrier by
construction. -/
theorem projected_mem_activeCarrier
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P X)
    (α : UA → P)
    (e : StructuralRamsey.Partite.ProjectedEmbedding A B α)
    (a : UA) :
    e.val a ∈ activeCarrier A B α :=
  ⟨e, ⟨a, rfl⟩⟩

/-- For an injective projection, the active carrier is contained in the union
of the selected parts.  The inclusion can be strict because boundary vertices
need not lie in an active A-copy. -/
theorem activeCarrier_subset_support
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) :
    activeCarrier A B α ⊆ B.support α := by
  intro x hx
  rcases hx with ⟨e, a, ha⟩
  refine ⟨a, ?_⟩
  change α a = B.part x
  have hp := e.property a
  rw [ha] at hp
  exact hp.symm

/-- Restrict a projected A-copy to an induced subsystem containing its whole
image. -/
def activeInduceProjected
    (A : RelStructure L UA)
    {B : StructuralRamsey.Partite.System L P X}
    {α : UA ↪ P}
    {S : Set X}
    (e : StructuralRamsey.Partite.ProjectedEmbedding A B α)
    (hRange : ∀ a : UA, e.val a ∈ S) :
    StructuralRamsey.Partite.ProjectedEmbedding A (B.induce S) α where
  val := {
    toFun := fun a => ⟨e.val a, hRange a⟩
    injective := by
      intro a b hab
      apply e.val.injective
      exact congrArg Subtype.val hab
    map_rel_iff := by
      intro R x
      change B.rel R (e.val ∘ x) ↔ A.rel R x
      exact e.val.map_rel_iff R x
  }
  property := by
    intro a
    exact e.property a

/-- A projected A-copy in the full picture agrees, after attachment, with the
same copy routed through the core whenever its image lies in the gluing
subsystem. -/
theorem activeAttachment_copy_comp
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P X)
    {α : UA ↪ P}
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) E)
    (i : I)
    (e : StructuralRamsey.Partite.ProjectedEmbedding A B α)
    (hRange : ∀ a : UA, e.val a ∈ S) :
    e.comp
        (StructuralRamsey.Partite.Attachment.copyEmbedding B S E f i) =
      ((activeInduceProjected A e hRange).comp (f i)).comp
        (StructuralRamsey.Partite.Attachment.coreEmbedding B S E f) := by
  apply Subtype.ext
  apply RelStructure.Embedding.ext
  intro a
  exact StructuralRamsey.Partite.Attachment.copy_extends
    B S E f i ⟨e.val a, hRange a⟩

/-- Picture property for an arbitrary induced active subsystem and an arbitrary
designated local Ramsey family.

The local hypothesis is deliberately phrased only on the projected A-copies
coming from the full old picture.  This is exactly what backward fusion needs,
and it permits the core witness to ignore boundary vertices that lie in the
selected parts but in no active A-copy. -/
theorem activeAttachment_pictureProperty
    (A : RelStructure L UA)
    (B : StructuralRamsey.Partite.System L P X)
    {α : UA ↪ P}
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (B.induce S) E)
    (κ : Type*)
    (hRange :
      ∀ e : StructuralRamsey.Partite.ProjectedEmbedding A B α,
        ∀ a : UA, e.val a ∈ S)
    (hLocal :
      ∀ χ :
          StructuralRamsey.Partite.ProjectedEmbedding A E α → κ,
        ∃ i : I,
          ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A B α,
            χ ((activeInduceProjected A e₁ (hRange e₁)).comp (f i)) =
              χ ((activeInduceProjected A e₂ (hRange e₂)).comp (f i))) :
    StructuralRamsey.Partite.PictureProperty A B α
      (StructuralRamsey.Partite.Attachment.attach B S E f) κ := by
  intro χ
  let core :=
    StructuralRamsey.Partite.Attachment.coreEmbedding B S E f
  let χCore :
      StructuralRamsey.Partite.ProjectedEmbedding A E α → κ :=
    fun e => χ (e.comp core)
  obtain ⟨i, hi⟩ := hLocal χCore
  refine ⟨StructuralRamsey.Partite.Attachment.copyEmbedding B S E f i, ?_⟩
  intro e₁ e₂
  rw [activeAttachment_copy_comp A B S E f i e₁ (hRange e₁),
      activeAttachment_copy_comp A B S E f i e₂ (hRange e₂)]
  exact hi e₁ e₂

/-- Full invariant-preserving active picture step.

This is the manuscript's standard extension shell: a local core over an
arbitrary active induced subsystem is freely attached to fresh copies of the
old picture.  Existing library lemmas preserve the partite projection and
irreducible-coverage invariant; the preceding theorem supplies the Ramsey
picture property. -/
theorem activeInducedPictureStep
    {VB : Type v}
    (A : RelStructure L UA)
    (B₀ : RelStructure L VB)
    (D₀ : RelStructure L P)
    (C₀ : StructuralRamsey.Partite.System L P X)
    {α : UA ↪ P}
    (S : Set X)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C₀.induce S) E)
    (κ : Type*)
    (hPartite : C₀.IsPartiteOver D₀)
    (hCover :
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy C₀ B₀ D₀)
    (hEPartite : E.IsPartiteOver D₀)
    (hECover :
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy E B₀ D₀)
    (hRange :
      ∀ e : StructuralRamsey.Partite.ProjectedEmbedding A C₀ α,
        ∀ a : UA, e.val a ∈ S)
    (hLocal :
      ∀ χ :
          StructuralRamsey.Partite.ProjectedEmbedding A E α → κ,
        ∃ i : I,
          ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A C₀ α,
            χ ((activeInduceProjected A e₁ (hRange e₁)).comp (f i)) =
              χ ((activeInduceProjected A e₂ (hRange e₂)).comp (f i))) :
    let C₁ := StructuralRamsey.Partite.Attachment.attach C₀ S E f
    C₁.IsPartiteOver D₀ ∧
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy C₁ B₀ D₀ ∧
      StructuralRamsey.Partite.PictureProperty A C₀ α C₁ κ := by
  let C₁ := StructuralRamsey.Partite.Attachment.attach C₀ S E f
  have hC₁Partite : C₁.IsPartiteOver D₀ :=
    StructuralRamsey.Partite.Attachment.attach_isPartiteOver
      C₀ S E f hPartite hEPartite
  have hC₁Cover :
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy C₁ B₀ D₀ :=
    StructuralRamsey.Partite.Induced.Attachment.attach_covers
      B₀ D₀ C₀ S E f hCover hECover
  have hPicture :
      StructuralRamsey.Partite.PictureProperty A C₀ α C₁ κ :=
    activeAttachment_pictureProperty
      A C₀ S E f κ hRange hLocal
  exact ⟨hC₁Partite, hC₁Cover, hPicture⟩

/-- The invariant-preserving picture step specialized to the manuscript's
canonical active subsystem P[e].  The range hypothesis is automatic from the
definition of `activeCarrier`. -/
theorem activeInducedPictureStep_onActiveCarrier
    {VB : Type v}
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
    (hEPartite : E.IsPartiteOver D₀)
    (hECover :
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy E B₀ D₀)
    (hLocal :
      ∀ χ :
          StructuralRamsey.Partite.ProjectedEmbedding A E α → κ,
        ∃ i : I,
          ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A C₀ α,
            χ ((activeInduceProjected A e₁
              (projected_mem_activeCarrier A C₀ α e₁)).comp (f i)) =
              χ ((activeInduceProjected A e₂
                (projected_mem_activeCarrier A C₀ α e₂)).comp (f i))) :
    let C₁ := StructuralRamsey.Partite.Attachment.attach
      C₀ (activeCarrier A C₀ α) E f
    C₁.IsPartiteOver D₀ ∧
      StructuralRamsey.Partite.Induced.CoversIrreduciblesBy C₁ B₀ D₀ ∧
      StructuralRamsey.Partite.PictureProperty A C₀ α C₁ κ := by
  exact activeInducedPictureStep
    A B₀ D₀ C₀ (activeCarrier A C₀ α) E f κ
    hPartite hCover hEPartite hECover
    (projected_mem_activeCarrier A C₀ α) hLocal


end StructuralRamsey.Girth
