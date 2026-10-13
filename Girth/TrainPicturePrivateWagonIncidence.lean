import Girth.TrainPictureWagonGenerators
import Girth.AttachmentGeometry

/-!
# Incidence geometry of private generated picture wagons

At a fixed wagon cut, a PRIVATE tagged wagon cannot contain a core
edge or an edge from another standard picture. Its whole vertex
carrier lies in precisely the indexed full standard picture.

Consequently, two private wagons with DIFFERENT standard indices
can meet only at vertices in the common core, by the standard free
attachment copy/copy intersection geometry. This is the crucial
first reduction in the allowed-part sibling-intersection proof:
all parameter violations away from the core must be entirely
inside one standard picture.

The theorem does not assert that core intersections already meet
the allowed-part parameter; those require the witness bridge
argument from acceptable order-one cycles.
-/

namespace StructuralRamsey.Girth

universe v
variable {E Core Old I OldEdge CoreEdge W : Type v}

/-- The complete vertex carrier of one explicitly labelled
generated wagon, not just the carrier of one of its edges. -/
def PictureTaggedWagonCarrier
    (tag : E → Core ⊕ (I × Old))
    (edgeCarrier : E → Set W)
    (t : Core ⊕ (I × Old)) : Set W :=
  {x | ∃ e : E, tag e = t ∧ x ∈ edgeCarrier e}

/-- Every vertex of a PRIVATE generated wagon belongs to the
full standard picture indexed by its private tag. -/
theorem picturePrivateWagonCarrier_subset_standard
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core)
    (tag : E → Core ⊕ (I × Old))
    (edgeCarrier : E → Set W)
    (copyCarrier : I → Set W)
    (hCoreTag : ∀ b, tag (coreEmbed b) = Sum.inl (coreClass b))
    (hStdTag : ∀ i a,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (hCover : ∀ e : E,
      (∃ b, e = coreEmbed b) ∨ ∃ i a, e = std i a)
    (hStdCarrier : ∀ i a, edgeCarrier (std i a) ⊆ copyCarrier i)
    (i : I) (a : Old) :
    PictureTaggedWagonCarrier tag edgeCarrier (Sum.inr (i, a)) ⊆
      copyCarrier i := by
  rintro x ⟨e, htag, hx⟩
  obtain ⟨b, hb, _hOld⟩ :=
    privatePictureTag_has_standard_owner
      coreEmbed std coreClass oldClass glue tag
      hCoreTag hStdTag hCover e i a htag
  rw [hb] at hx
  exact hStdCarrier i b hx

/-- Distinct private standard-copy wagon indices can intersect
ONLY in the core, not at any vertex private to either copy. -/
theorem pictureDistinctPrivateWagons_intersect_subset_core
    (coreEmbed : CoreEdge → E)
    (std : I → OldEdge → E)
    (coreClass : CoreEdge → Core)
    (oldClass : OldEdge → Old)
    (glue : I → Old → Option Core)
    (tag : E → Core ⊕ (I × Old))
    (edgeCarrier : E → Set W)
    (copyCarrier : I → Set W)
    (coreVertexCarrier : Set W)
    (hCoreTag : ∀ b, tag (coreEmbed b) = Sum.inl (coreClass b))
    (hStdTag : ∀ i a,
      tag (std i a) = gluedStandardNode glue i (oldClass a))
    (hCover : ∀ e : E,
      (∃ b, e = coreEmbed b) ∨ ∃ i a, e = std i a)
    (hStdCarrier : ∀ i a, edgeCarrier (std i a) ⊆ copyCarrier i)
    (hInter : ∀ i j : I, i ≠ j →
      copyCarrier i ∩ copyCarrier j ⊆ coreVertexCarrier)
    (i j : I) (hij : i ≠ j) (a b : Old) :
    PictureTaggedWagonCarrier tag edgeCarrier (Sum.inr (i, a)) ∩
      PictureTaggedWagonCarrier tag edgeCarrier (Sum.inr (j, b)) ⊆
        coreVertexCarrier := by
  intro x hx
  apply hInter i j hij
  constructor
  · exact picturePrivateWagonCarrier_subset_standard
      coreEmbed std coreClass oldClass glue tag
      edgeCarrier copyCarrier
      hCoreTag hStdTag hCover hStdCarrier i a hx.1
  · exact picturePrivateWagonCarrier_subset_standard
      coreEmbed std coreClass oldClass glue tag
      edgeCarrier copyCarrier
      hCoreTag hStdTag hCover hStdCarrier j b hx.2

end StructuralRamsey.Girth
