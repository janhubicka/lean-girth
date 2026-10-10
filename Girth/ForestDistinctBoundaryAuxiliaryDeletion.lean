import Girth.ForestDistinctBoundaryAugmented
import Girth.ForestAuxiliaryDeletion

/-!
# Delete incidence auxiliaries after obtaining their join tree

The direct forest increment first builds a forest on the augmented
incidence index type: selected true support members, distinct local
boundary-edge nodes, and formal boundary vertex nodes.

Every non-selected member is a one-edge auxiliary piece, so
ForestOfCopies.restrict_of_oneEdge_outside applies. This does NOT use
the false assertion that arbitrary subfamilies of a forest remain
forests. No graph contraction is required in this deletion step.

Combined with pairwiseAllowed_augmentedBoundaryPieces, the sole
remaining geometric obligation in the all-distinct case is the
RUNNING-INTERSECTION JOIN TREE of the augmented incidence family.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E V : Type v}

/-- A forest on the full boundary-incidence family restricts to the
actual selected pieces: every deleted auxiliary is a one-edge piece,
including formal singleton nodes. -/
theorem ForestOfCopies.selected_of_augmentedBoundaryPieces
    [Fintype I] [Fintype E] [Fintype V]
    (selected : I → HypergraphPiece W)
    (edge : E → Set W)
    (vertex : V → W)
    (hForest :
      ForestOfCopies
        (augmentedBoundaryPieces selected edge vertex)) :
    ForestOfCopies selected := by
  classical
  let keep : Finset (I ⊕ (E ⊕ V)) :=
    Finset.univ.image (fun i : I => Sum.inl i)
  have hOne :
      ∀ z : I ⊕ (E ⊕ V), z ∉ keep →
        (augmentedBoundaryPieces selected edge vertex z).IsOneEdge := by
    intro z hz
    cases z with
    | inl i =>
      exfalso
      apply hz
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    | inr ev =>
      cases ev with
      | inl e =>
        exact HypergraphPiece.oneEdge_isOneEdge (edge e)
      | inr x =>
        exact HypergraphPiece.oneEdge_isOneEdge
          ({vertex x} : Set W)
  have hRemaining :=
    hForest.restrict_of_oneEdge_outside keep hOne
  let toKeep : I ≃
      {z : I ⊕ (E ⊕ V) // z ∈ keep} := {
    toFun := fun i =>
      ⟨Sum.inl i, Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩⟩
    invFun := fun z =>
      match z.1 with
      | .inl i => i
      | .inr _ => False.elim (by
          obtain ⟨i, _hi, hEq⟩ := Finset.mem_image.mp z.2
          cases hEq)
    left_inv := by
      intro i
      rfl
    right_inv := by
      intro z
      cases z with
      | mk val hval =>
        cases val with
        | inl i =>
          apply Subtype.ext
          rfl
        | inr ev =>
          obtain ⟨i, _hi, hEq⟩ := Finset.mem_image.mp hval
          cases hEq
  }
  have hSelected :
      ForestOfCopies
        (fun i : I =>
          augmentedBoundaryPieces selected edge vertex (toKeep i).1) :=
    hRemaining.reindex toKeep
  change ForestOfCopies selected at hSelected
  exact hSelected

end StructuralRamsey.Girth
