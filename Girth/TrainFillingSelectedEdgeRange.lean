import Girth.TrainFillingSelectedStrongCover

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
      (congrArg (fun p : U.OldEdge × U.TemplateEdge => p.2) hp)

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

/-- If a contracted selected old copy is strong, the canonical selected
filled-edge embedding covers exactly the ambient filled edges whose
physical carriers are contained in the selected vertex carrier.

This removes the exact `copyEdges_eq` field from the application:
old strongness and edge containment suffice. The ambient filled-edge
type is unchanged; in particular no outside edge is pruned. -/
theorem selectedFilledEdgeEmbedding_range_eq_contained
    (β : S ↪ U.OldEdge)
    (carrier : Set V)
    (hSelectedContained : ∀ s : S, (β s).1 ⊆ carrier)
    (hOldStrong : ∀ f : U.OldEdge,
      ¬ (f.1 ∩ carrier).Subsingleton → f ∈ Set.range β) :
    Set.range (U.selectedFilledEdgeEmbedding β) =
      {e : U.toTrainFilling.NewEdge | e.1 ⊆ carrier} := by
  calc
    Set.range (U.selectedFilledEdgeEmbedding β) =
        {e | U.toTrainFilling.cover e ∈ Set.range β} :=
      U.selectedFilledEdgeEmbedding_range β
    _ = {e | e.1 ⊆ carrier} :=
      (U.generatedEdges_selected_exact carrier (Set.range β)
        (by
          rintro f ⟨s, rfl⟩
          exact hSelectedContained s) hOldStrong).symm

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
  localPlacement : S → (X ↪ W)
  vertex_local : ∀ s x,
    vertex (localPlacement s x) = U.place (oldEdge s) x

namespace SelectedContractedPlacement

variable {W : Type v}

/-- Local physical edge carriers inside the contracted selected copy. -/
def sourcePhysicalCarrier
    (R : U.SelectedContractedPlacement (S := S) W)
    (c : S × U.TemplateEdge) : Set W :=
  R.localPlacement c.1 '' c.2.1

/-- The actual global physical filled edge carrier is exactly the
image of its source local physical carrier under the selected M-copy
vertex embedding. No ambient edges are discarded or reinterpreted. -/
theorem edgeCarrier_eq_image
    (R : U.SelectedContractedPlacement (S := S) W)
    (c : S × U.TemplateEdge) :
    U.imageCarrier (R.oldEdge c.1, c.2) =
      R.vertex '' sourcePhysicalCarrier U R c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R.localPlacement c.1 x, ⟨x, hx, rfl⟩,
      R.vertex_local c.1 x⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (R.vertex_local c.1 x).symm⟩

/-- Consequently the canonical physical edge embedding constructed
from the selected old edge map automatically has its exact carrier
transport. This is the second realization field after exact range. -/
theorem physicalEdge_carrier_eq_image
    (R : U.SelectedContractedPlacement (S := S) W)
    (c : S × U.TemplateEdge) :
    (U.selectedFilledEdgeEmbedding R.oldEdge c).1 =
      R.vertex '' sourcePhysicalCarrier U R c := by
  change U.imageCarrier (R.oldEdge c.1, c.2) =
    R.vertex '' sourcePhysicalCarrier U R c
  exact edgeCarrier_eq_image U R c

end SelectedContractedPlacement

end StructuralRamsey.Girth.UniformFillingData
