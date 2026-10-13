import Girth.AttachmentGeometry

/-!
# Every off-core vertex has ONE old standard picture edge owner

A free picture attachment's physical edge set is covered by its
core edges and its full standard-copy edge images. A physical vertex
outside the witness core cannot lie in a core edge. Two different
standard copies meet only in the core.

Consequently ANY two actual physical support edges meeting at a
vertex outside the core belong to the SAME standard picture.
This holds whether their generated wagon ancestors are PRIVATE
or shared through an H-wagon; no wagon-tag analysis is needed.

This directly simplifies Section 11's allowed sibling
intersection proof at vertices outside H. The remaining difficult
branch is a vertex IN the core, where the order-one witness bridge
must force compatible child ownership.
-/

namespace StructuralRamsey.Girth

universe v
variable {E CoreEdge OldEdge I W : Type v}

/-- In any free picture satisfying the genuine core/standard
edge-cover and core-intersection geometry, two edges sharing
a vertex outside the core have a common STANDARD-PICTURE owner.
No conditions on wagon equivalence are needed. -/
theorem picture_offCore_incident_edges_same_standard
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (edgeCarrier : E → Set W)
    (copyCarrier : I → Set W)
    (coreCarrier : Set W)
    (hCover : ∀ e : E,
      (∃ c, e = coreEmbed c) ∨ ∃ i a, e = std i a)
    (hCoreCarrier : ∀ c, edgeCarrier (coreEmbed c) ⊆ coreCarrier)
    (hStdCarrier : ∀ i a, edgeCarrier (std i a) ⊆ copyCarrier i)
    (hCopyInter : ∀ i j : I, i ≠ j →
      copyCarrier i ∩ copyCarrier j ⊆ coreCarrier)
    (x : W) (hx : x ∉ coreCarrier)
    (e f : E)
    (he : x ∈ edgeCarrier e)
    (hf : x ∈ edgeCarrier f) :
    ∃ i : I, ∃ a b : OldEdge,
      e = std i a ∧ f = std i b := by
  rcases hCover e with ⟨c, hc⟩ | ⟨i, a, ha⟩
  · rw [hc] at he
    exact False.elim (hx (hCoreCarrier c he))
  · rcases hCover f with ⟨d, hd⟩ | ⟨j, b, hb⟩
    · rw [hd] at hf
      exact False.elim (hx (hCoreCarrier d hf))
    · have hxi : x ∈ copyCarrier i := hStdCarrier i a (by
        rw [ha] at he
        exact he)
      have hxj : x ∈ copyCarrier j := hStdCarrier j b (by
        rw [hb] at hf
        exact hf)
      have hij : i = j := by
        by_contra hne
        exact hx (hCopyInter i j hne ⟨hxi, hxj⟩)
      subst j
      exact ⟨i, a, b, ha, hb⟩

/-- The standard-copy index of ANY off-core incident support edge
is unique. A different index would meet the first outside the core,
contradicting the free-attachment geometry. -/
theorem picture_offCore_standard_index_unique
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (edgeCarrier : E → Set W)
    (copyCarrier : I → Set W)
    (coreCarrier : Set W)
    (hCover : ∀ e : E,
      (∃ c, e = coreEmbed c) ∨ ∃ i a, e = std i a)
    (hCoreCarrier : ∀ c, edgeCarrier (coreEmbed c) ⊆ coreCarrier)
    (hStdCarrier : ∀ i a, edgeCarrier (std i a) ⊆ copyCarrier i)
    (hCopyInter : ∀ i j : I, i ≠ j →
      copyCarrier i ∩ copyCarrier j ⊆ coreCarrier)
    (x : W) (hx : x ∉ coreCarrier)
    (i j : I) (a b : OldEdge)
    (hia : x ∈ edgeCarrier (std i a))
    (hjb : x ∈ edgeCarrier (std j b)) :
    i = j := by
  obtain ⟨k, c, d, h1, h2⟩ :=
    picture_offCore_incident_edges_same_standard
      coreEmbed std edgeCarrier copyCarrier coreCarrier
      hCover hCoreCarrier hStdCarrier hCopyInter x hx
      (std i a) (std j b) hia hjb
  have hxi : x ∈ copyCarrier i := hStdCarrier i a hia
  have hxk : x ∈ copyCarrier k := hStdCarrier k c (by
    rw [← h1]
    exact hia)
  have hik : i = k := by
    by_contra hne
    exact hx (hCopyInter i k hne ⟨hxi, hxk⟩)
  have hxj : x ∈ copyCarrier j := hStdCarrier j b hjb
  have hkj : k = j := by
    by_contra hne
    exact hx (hCopyInter k j hne ⟨hxk, hxj⟩)
  exact hik.trans hkj

end StructuralRamsey.Girth
