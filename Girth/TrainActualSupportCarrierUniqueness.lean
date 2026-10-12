import Girth.AttachmentGeometry

/-!
# Injectivity of real physical support carriers in free attachments

The actual physical support edge of a standard copy is the IMAGE
of an old edge carrier under its injective vertex map. If the old
carrier contains any vertex outside the gluing subsystem, its
physical image contains a genuinely private vertex. Thus it cannot
equal a core support edge, and equal private support images cannot
have different standard-copy indices.

These facts avoid identifying distinct actual support edges by
arbitrary copy labels or merely equal wagon carriers. They supply
the injectivity half of the concrete physical edge-pushout model.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {Old Core I : Type v}

/-- An injective vertex map induces an injective map on SETS of
vertices. A support edge is identified with its actual carrier,
rather than with a possibly nonrigid embedding of its template. -/
theorem supportCarrier_image_eq_of_injective
    {X Y : Type v} (g : X → Y) (hg : Function.Injective g)
    {T U : Set X} (h : g '' T = g '' U) : T = U := by
  ext x
  constructor
  · intro hx
    have hh : g x ∈ g '' U := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hh
    have hYX : y = x := hg hxy
    simpa [hYX] using hy
  · intro hx
    have hh : g x ∈ g '' T := by
      rw [h]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hh
    have hYX : y = x := hg hxy
    simpa [hYX] using hy

/-- An old carrier containing a PRIVATE vertex cannot become a
core carrier under attachment. -/
theorem attachment_privateStandardCarrier_ne_core
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (T : Set Old) (U : Set Core)
    (hPrivate : ∃ x : Old, x ∈ T ∧ x ∉ S) :
    ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T) ≠
      ((fun y : Core =>
        (RelStructure.Attachment.coreEmbedding B S D f) y) '' U) := by
  intro hSame
  obtain ⟨x, hx, hxNot⟩ := hPrivate
  have hCore :
      (RelStructure.Attachment.copyEmbedding B S D f i) x ∈
        ((fun y : Core =>
          (RelStructure.Attachment.coreEmbedding B S D f) y) '' U) := by
    rw [← hSame]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, _hy, hEq⟩ := hCore
  have hCopy :
      RelStructure.Attachment.copyMap B S D f i x =
        Sum.inl y := by
    exact hEq.symm
  exact hxNot (RelStructure.Attachment.mem_of_copyMap_eq_inl hCopy)

/-- If two standard physical support carriers have the same image
and the FIRST one has a private vertex, they must come from the
SAME standard picture. -/
theorem attachment_privateStandardCarrier_unique_index
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i j : I) (T U : Set Old)
    (hPrivate : ∃ x : Old, x ∈ T ∧ x ∉ S)
    (hSame :
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T) =
      ((fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f j) x) '' U)) :
    i = j := by
  obtain ⟨x, hxT, hxNot⟩ := hPrivate
  have hz :
      (RelStructure.Attachment.copyEmbedding B S D f i) x ∈
        ((fun y : Old =>
          (RelStructure.Attachment.copyEmbedding B S D f j) y) '' U) := by
    rw [← hSame]
    exact ⟨x, hxT, rfl⟩
  obtain ⟨y, _hy, hxy⟩ := hz
  have hMap :
      RelStructure.Attachment.copyMap B S D f i x =
        RelStructure.Attachment.copyMap B S D f j y := by
    exact hxy.symm
  exact RelStructure.Attachment.index_eq_of_outside
    (B := B) (S := S) (D := D) (f := f) hxNot hMap

/-- Within one standard picture, image equality is equivalent to
equality of the OLD support edge carriers. -/
theorem attachment_standardCarrier_image_eq_iff
    (B : RelStructure L Old)
    (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (i : I) (T U : Set Old) :
    ((fun x : Old =>
      (RelStructure.Attachment.copyEmbedding B S D f i) x) '' T) =
    ((fun x : Old =>
      (RelStructure.Attachment.copyEmbedding B S D f i) x) '' U)
      ↔ T = U := by
  constructor
  · intro h
    exact supportCarrier_image_eq_of_injective
      (fun x : Old =>
        (RelStructure.Attachment.copyEmbedding B S D f i) x)
      (RelStructure.Attachment.copyEmbedding B S D f i).injective h
  · intro h
    rw [h]

end StructuralRamsey.Girth
