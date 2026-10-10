import Girth.ForestDistinctBoundaryAugmented
import Girth.ForestAuxiliaryDeletion

/-!
# Remove every temporary incidence node from an augmented forest

For the all-distinct case of the direct forest increment we use
three labelled kinds of members: actual selected A/B support pieces,
temporary physical boundary edges, and temporary singleton vertices.
The latter two kinds are ONE-EDGE hypergraph pieces, even when the
singleton is not a genuine ambient A-support edge.

Once a join tree for this augmented family has been constructed,
the established one-edge deletion theorem removes the entire finite
auxiliary family without harming the forest property. This proof
does NOT make the false assertion that arbitrary subfamilies of
forests remain forests.

The remaining task is constructing the augmented join tree from
the girth-bounded boundary incidence graph.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- The selected members form a forest whenever the temporary
three-sort incidence family is a forest. All auxiliary removals
are justified by one-edge deletion, not subfamily heredity. -/
theorem selectedForest_of_augmentedBoundaryForest
    [Fintype I] [Fintype E] [Fintype V]
    (selected : I → HypergraphPiece W)
    (edge : E → Set W)
    (vertex : V → W)
    (hForest :
      ForestOfCopies (augmentedBoundaryPieces selected edge vertex)) :
    ForestOfCopies selected := by
  classical
  let T := I ⊕ (E ⊕ V)
  let keep : Finset T := Finset.univ.image
    (Sum.inl : I → T)
  have hInl : ∀ i : I, (Sum.inl i : T) ∈ keep := by
    intro i
    simp [keep]
  have hInr : ∀ j : E ⊕ V, (Sum.inr j : T) ∉ keep := by
    intro j
    simp [keep]
  have hOne :
      ∀ z : T, z ∉ keep →
        (augmentedBoundaryPieces selected edge vertex z).IsOneEdge := by
    intro z hz
    cases z with
    | inl i =>
        exact (hz (hInl i)).elim
    | inr z =>
        cases z with
        | inl e =>
            change (HypergraphPiece.oneEdge (edge e)).IsOneEdge
            rfl
        | inr v =>
            change (HypergraphPiece.oneEdge ({vertex v} : Set W)).IsOneEdge
            rfl
  have hRestrict :
      ForestOfCopies
        (fun z : {z : T // z ∈ keep} =>
          augmentedBoundaryPieces selected edge vertex z.1) :=
    hForest.restrict_of_oneEdge_outside keep hOne
  let relabel : I ≃ {z : T // z ∈ keep} :=
    { toFun := fun i => ⟨Sum.inl i, hInl i⟩
      invFun := fun z =>
        match hz : z.1 with
        | .inl i => i
        | .inr j => False.elim (hInr j (by
            simpa [hz] using z.2))
      left_inv := by
        intro i
        rfl
      right_inv := by
        intro z
        cases z with
        | mk z hz =>
            cases z with
            | inl i =>
                apply Subtype.ext
                rfl
            | inr j =>
                exact (hInr j hz).elim }
  have hResult := hRestrict.reindex relabel
  simpa only [augmentedBoundaryPieces] using hResult

end StructuralRamsey.Girth
