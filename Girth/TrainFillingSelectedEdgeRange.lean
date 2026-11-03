import Girth.TrainFillingTemplateConstruction

set_option Elab.async false

/-!
# Physical filled-edge realization of a selected contracted copy

A selected M-copy gives an injective map of its contracted physical edges
into the old N-edge family. A uniform filling replaces every old edge by
every template edge. The already checked physical edge equivalence makes
the induced map on all (source edge, local template edge) pairs injective.

Its image is EXACTLY the full filled-edge family whose old cover belongs
to the selected M-copy. No edge is omitted or arbitrarily assigned to an
old cover, including when the old selected edge family is empty.

This proves the physical EDGE-map and exact edge-coverage fields required
by a global parentwise realization. Vertex maps, wagon-map compatibility
and actual selected-copy transport are separate obligations.
-/

namespace StructuralRamsey.Girth.UniformFillingData

universe v
variable {V X S : Type v} (U : UniformFillingData V X)

/-- Physical new edges over the image of a selected contracted old edge
embedding, using all local template edges with their actual labels. -/
noncomputable def selectedFilledEdgeEmbedding
    (β : S ↪ U.OldEdge) :
    (S × U.TemplateEdge) ↪ U.toTrainFilling.NewEdge where
  toFun := fun a => U.edgeEquiv (β a.1, a.2)
  inj' := by
    intro a b h
    have hp : (β a.1, a.2) = (β b.1, b.2) :=
      U.edgeEquiv.injective h
    exact Prod.ext
      (β.injective (congrArg Prod.fst hp))
      (congrArg Prod.snd hp)

/-- The selected physical edge keeps its actual old edge as unique cover. -/
@[simp] theorem selectedFilledEdgeEmbedding_cover
    (β : S ↪ U.OldEdge) (s : S) (a : U.TemplateEdge) :
    U.toTrainFilling.cover (U.selectedFilledEdgeEmbedding β (s,a)) = β s :=
  U.edgeEquiv_cover (β s, a)

/-- Exact range identity: the image includes ALL filled physical edges
over the selected old edges, and includes NO others. This remains true for
empty local or old edge types, without a nonemptiness assumption. -/
theorem selectedFilledEdgeEmbedding_range
    (β : S ↪ U.OldEdge) :
    Set.range (U.selectedFilledEdgeEmbedding β) =
      {e : U.toTrainFilling.NewEdge |
        U.toTrainFilling.cover e ∈ Set.range β} := by
  ext e
  constructor
  · rintro ⟨⟨s, a⟩, rfl⟩
    exact ⟨s, (U.selectedFilledEdgeEmbedding_cover β s a).symm⟩
  · intro he
    obtain ⟨s, hs⟩ := he
    refine ⟨(s, (U.decode e).2), ?_⟩
    change U.encode (β s, (U.decode e).2) = e
    have hCover : β s = (U.decode e).1 := by
      change β s = (U.decode e).1 at hs
      exact hs
    rw [hCover]
    exact U.encode_decode e

/-- Every source/local pair maps to its literal physical carrier:
selected-copy edge images require no independent decoding data. -/
@[simp] theorem selectedFilledEdgeEmbedding_carrier
    (β : S ↪ U.OldEdge) (s : S) (a : U.TemplateEdge) :
    (U.selectedFilledEdgeEmbedding β (s,a)).1 =
      U.imageCarrier (β s, a) := rfl

/-- The complete selected filled-edge image is precisely the ordinary
cover pullback of the contracted selected old-edge image. -/
theorem selectedFilledEdges_eq_coverPullback
    (β : S ↪ U.OldEdge)
    (selected : Set U.toTrainFilling.NewEdge)
    (hSelected :
      selected = {e | U.toTrainFilling.cover e ∈ Set.range β}) :
    selected = Set.range (U.selectedFilledEdgeEmbedding β) := by
  rw [hSelected, U.selectedFilledEdgeEmbedding_range β]


/-- An actual contracted M-copy provides a vertex embedding and local
X-coordinate maps; their equality with the canonical N placements is
the precise remaining compatibility requirement. The full physical
new-edge carrier identity is then a CONCLUSION, not a field. -/
structure SelectedContractedPlacement (W : Type v) where
  vertex : W ↪ V
  oldEdge : S ↪ U.OldEdge
  local : S → X ↪ W
  vertex_local : ∀ s x,
    vertex (local s x) = U.place (oldEdge s) x

namespace SelectedContractedPlacement

variable {W : Type v} (R : U.SelectedContractedPlacement (S := S) W)

/-- Local physical edge carriers inside the contracted selected copy. -/
def sourcePhysicalCarrier (c : S × U.TemplateEdge) : Set W :=
  R.local c.1 '' c.2.1

/-- The actual global physical filled edge carrier is exactly the
image of its source local physical carrier under the selected M-copy
vertex embedding. No ambient edges are discarded or reinterpreted. -/
theorem edgeCarrier_eq_image (c : S × U.TemplateEdge) :
    U.imageCarrier (R.oldEdge c.1, c.2) =
      R.vertex '' R.sourcePhysicalCarrier c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R.local c.1 x, ⟨x, hx, rfl⟩,
      R.vertex_local c.1 x⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (R.vertex_local c.1 x).symm⟩

/-- Consequently the canonical physical edge embedding constructed
from the selected old edge map automatically has its exact carrier
transport. This is the second realization field after exact range. -/
theorem physicalEdge_carrier_eq_image (c : S × U.TemplateEdge) :
    (U.selectedFilledEdgeEmbedding R.oldEdge c).1 =
      R.vertex '' R.sourcePhysicalCarrier c := by
  change U.imageCarrier (R.oldEdge c.1, c.2) =
    R.vertex '' R.sourcePhysicalCarrier c
  exact R.edgeCarrier_eq_image c

end SelectedContractedPlacement

end StructuralRamsey.Girth.UniformFillingData
