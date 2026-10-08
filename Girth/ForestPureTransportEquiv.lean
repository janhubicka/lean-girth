import Girth.ForestImage
import Mathlib.Tactic

/-!
# Cancelling transport-only stages of a forest of B-copies

The existing library shows that a forest remains a forest after every
injective transport of its entire ambient vertex universe. The converse
is equally important for diary normalization: when all marked pieces
of a selected configuration are carried into one standard picture by
the SAME injective embedding, no new forest incidence obstruction is
created or removed.

We prove exact reflection of allowed pairwise intersections, reflect the
running-intersection join tree on its unchanged member index tree,
and hence obtain an iff for the complete ForestOfCopies predicate.

The result requires one common injective transport for the whole
configuration. It does not apply to new contacts between different
standard copies and does not erase mandatory ancestral parameters
from an unrelated raw free-history code.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Z ι : Type v}

/-- Injectivity of an ambient vertex embedding makes its operation on
subsets injective as well, even without any finiteness assumptions. -/
private theorem image_set_eq_iff_injective
    (φ : W ↪ Z) (A B : Set W) :
    φ '' A = φ '' B ↔ A = B := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      have hImage : φ x ∈ φ '' B := by
        rw [← h]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hImage
      have hEq : x = y := φ.injective hxy.symm
      simpa [hEq] using hy
    · intro y hy
      have hImage : φ y ∈ φ '' A := by
        rw [h]
        exact ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hImage
      have hEq : x = y := φ.injective hxy
      simpa [hEq] using hx
  · intro h
    rw [h]

/-- Reflect permitted singleton/A-edge intersections through the SAME
injective transport applied to both pieces. -/
theorem AllowedIntersection.of_map
    (F G : HypergraphPiece W) (φ : W ↪ Z)
    (h : AllowedIntersection (F.map φ) (G.map φ)) :
    AllowedIntersection F G := by
  rcases h with hSmall | ⟨mappedEdge, hF, hG, hInter⟩
  · left
    intro x hx y hy
    apply φ.injective
    have hA : φ x ∈ (F.map φ).carrier ∩ (G.map φ).carrier :=
      ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    have hB : φ y ∈ (F.map φ).carrier ∩ (G.map φ).carrier :=
      ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
    exact hSmall hA hB
  · obtain ⟨a, ha, hImgA⟩ := hF
    obtain ⟨b, hb, hImgB⟩ := hG
    have hAB : a = b :=
      (image_set_eq_iff_injective φ a b).mp
        (hImgA.symm.trans hImgB)
    have hG' : a ∈ G.edges := by
      rw [hAB]
      exact hb
    have hCarrier : φ '' (F.carrier ∩ G.carrier) = φ '' a := by
      calc
        φ '' (F.carrier ∩ G.carrier) =
            (φ '' F.carrier) ∩ (φ '' G.carrier) :=
          Set.image_inter φ.injective
        _ = (F.map φ).carrier ∩ (G.map φ).carrier := rfl
        _ = mappedEdge := hInter
        _ = φ '' a := hImgA
    right
    exact ⟨a, ha, hG',
      (image_set_eq_iff_injective φ _ _).mp hCarrier⟩

/-- The join tree of a transported family already has the correct
occurrence subtrees in the original family. -/
def JoinTree.unmap
    {F : ι → HypergraphPiece W}
    (J : JoinTree (fun i => (F i).map φ))
    (φ : W ↪ Z) : JoinTree F where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro x
    have hOcc :
        {i : ι | x ∈ (F i).carrier} =
          {i : ι | φ x ∈ ((F i).map φ).carrier} := by
      ext i
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        have heq : y = x := φ.injective hxy
        simpa [heq] using hy
    rw [hOcc]
    exact J.running (φ x)

/-- A forest of transported pieces reflects to a forest of the
original pieces. All ambient vertices and piece supports are treated
at once; no selected-member enumeration is needed. -/
theorem ForestOfCopies.unmap
    {F : ι → HypergraphPiece W} (φ : W ↪ Z)
    (hForest : ForestOfCopies (fun i => (F i).map φ)) :
    ForestOfCopies F := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact AllowedIntersection.of_map (F i) (F j) φ
      (hForest.pairwiseAllowed hij)
  · rcases hForest.2 with hEmpty | ⟨J⟩
    · exact Or.inl hEmpty
    · exact Or.inr ⟨J.unmap φ⟩

/-- A pure injective standard-copy transport has NO effect on full
foresthood. In particular a finite chain of such transport-only steps
can be contracted at the level of its realised forest geometry. -/
theorem forestOfCopies_map_iff
    {F : ι → HypergraphPiece W} (φ : W ↪ Z) :
    ForestOfCopies (fun i => (F i).map φ) ↔ ForestOfCopies F := by
  constructor
  · exact ForestOfCopies.unmap φ
  · intro hForest
    exact hForest.map φ

end StructuralRamsey.Girth
