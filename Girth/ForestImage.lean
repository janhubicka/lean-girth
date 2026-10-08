import Girth.ForestSingleEdge

/-! # Transporting a finite forest through an injective embedding

Local completion forests are built in individual old standard pictures and
then transported into the attached picture.  Their combinatorial forest
property is invariant under injective maps of the underlying vertices.  This
module makes the transport explicit for hypergraph pieces and join trees.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Z ι : Type v}

/-- Image of a support piece under an injective map.  Both carrier and support
edges are transported, so full-edge intersections remain visible. -/
def HypergraphPiece.map
    (F : HypergraphPiece W) (φ : W ↪ Z) :
    HypergraphPiece Z where
  carrier := φ '' F.carrier
  edges := {e | ∃ e₀ : Set W, e₀ ∈ F.edges ∧ e = φ '' e₀}
  edge_subset_carrier := by
    intro e he z hz
    rcases he with ⟨e₀, he₀, rfl⟩
    rcases hz with ⟨w, hw, rfl⟩
    exact ⟨w, F.edge_subset he₀ hw, rfl⟩

/-- Transport also preserves the special one-edge auxiliary pieces that
the circulation proof is allowed to remove after assembly. -/
theorem HypergraphPiece.map_isOneEdge
    (F : HypergraphPiece W) (φ : W ↪ Z)
    (hF : F.IsOneEdge) :
    (F.map φ).IsOneEdge := by
  unfold HypergraphPiece.IsOneEdge
  ext e
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    have heq : e₀ = F.carrier := by
      rw [hF] at he₀
      simpa using he₀
    simp [HypergraphPiece.map, heq]
  · intro he
    have heq : e = φ '' F.carrier := by
      simpa [HypergraphPiece.map] using he
    exact ⟨F.carrier, by rw [hF]; simp, heq⟩

@[simp] theorem HypergraphPiece.map_carrier
    (F : HypergraphPiece W) (φ : W ↪ Z) :
    (F.map φ).carrier = φ '' F.carrier := rfl

/-- Allowed intersections survive injective transport. -/
theorem AllowedIntersection.map
    {F G : HypergraphPiece W}
    (h : AllowedIntersection F G)
    (φ : W ↪ Z) :
    AllowedIntersection (F.map φ) (G.map φ) := by
  rcases h with hSmall | ⟨e, heF, heG, hInter⟩
  · left
    intro x hx y hy
    have hEq :
        (F.map φ).carrier ∩ (G.map φ).carrier =
          φ '' (F.carrier ∩ G.carrier) := by
      change (φ '' F.carrier) ∩ (φ '' G.carrier) =
        φ '' (F.carrier ∩ G.carrier)
      exact (Set.image_inter φ.injective).symm
    rw [hEq] at hx hy
    rcases hx with ⟨u, hu, rfl⟩
    rcases hy with ⟨v, hv, rfl⟩
    exact congrArg φ (hSmall hu hv)
  · right
    refine ⟨φ '' e, ?_, ?_, ?_⟩
    · exact ⟨e, heF, rfl⟩
    · exact ⟨e, heG, rfl⟩
    · change (φ '' F.carrier) ∩ (φ '' G.carrier) = φ '' e
      rw [← Set.image_inter φ.injective, hInter]

/-- A join tree retains exactly the same index tree after injective
transport; every vertex occurrence subtree is either an old occurrence
subtree or empty. -/
def JoinTree.map
    {F : ι → HypergraphPiece W}
    (J : JoinTree F) (φ : W ↪ Z) :
    JoinTree (fun i => (F i).map φ) where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro z
    by_cases hz : z ∈ Set.range φ
    · rcases hz with ⟨w, rfl⟩
      have hOcc :
          {i : ι | φ w ∈ ((F i).map φ).carrier} =
            {i : ι | w ∈ (F i).carrier} := by
        ext i
        constructor
        · rintro ⟨u, hu, heq⟩
          have huw : u = w := φ.injective heq
          simpa [huw] using hu
        · intro hw
          exact ⟨w, hw, rfl⟩
      rw [hOcc]
      exact J.running w
    · have hEmpty :
          {i : ι | z ∈ ((F i).map φ).carrier} =
            (∅ : Set ι) := by
        ext i
        constructor
        · rintro ⟨w, hw, heq⟩
          exact (hz ⟨w, heq⟩).elim
        · intro hi
          simp at hi
      rw [hEmpty]
      intro a b
      have absurd : False := by simpa using a.2
      exact absurd.elim

/-- The image of a forest under an injective map is again a forest. -/
theorem ForestOfCopies.map
    {F : ι → HypergraphPiece W}
    (hF : ForestOfCopies F)
    (φ : W ↪ Z) :
    ForestOfCopies (fun i => (F i).map φ) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact AllowedIntersection.map (hF.pairwiseAllowed hij) φ
  · rcases hF.2 with hEmpty | hTree
    · exact Or.inl hEmpty
    · cases hTree with
      | intro J => exact Or.inr ⟨J.map φ⟩

end StructuralRamsey.Girth
