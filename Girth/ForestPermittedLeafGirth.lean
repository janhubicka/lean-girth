import Girth.ForestLeafDeletion
import Girth.BergeGlue
import Mathlib.Tactic

/-!
# Girth and supported separators when peeling a leaf of a B-copy forest

The join-tree enumeration theorem identifies the overlap of any leaf
with the ENTIRE rest union with its overlap with its single parent.
Pairwise allowed intersections then force this overlap to be a
singleton or a COMPLETE support edge in the parent and leaf.

The pure Berge singleton/edge gluing lemmas therefore allow one to
reconstruct ambient support girth from the leaf-deleted forest and
the intrinsic support of its leaf, with no extra locality hypotheses.

This is the exact local induction step for the theorem that every
finite forest of B-support pieces is girth-preserving. The full
well-founded leaf-enumeration induction is kept separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- The union of support edge families decomposes into the support
edges of any distinguished member and of all remaining members. -/
theorem forestEdges_eq_leaf_union_rest
    (F : ι → HypergraphPiece W) (leaf : ι) :
    (⋃ i : ι, (F i).edges) =
      (F leaf).edges ∪
      (⋃ j : {i : ι // i ≠ leaf}, (F j.1).edges) := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    by_cases hil : i = leaf
    · subst i
      exact Or.inl hi
    · exact Or.inr
        (Set.mem_iUnion.mpr ⟨⟨i, hil⟩, hi⟩)
  · intro he
    rcases he with heLeaf | heRest
    · exact Set.mem_iUnion.mpr ⟨leaf, heLeaf⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heRest
      exact Set.mem_iUnion.mpr ⟨j.1, hj⟩

/-- The leaf support edges can meet support edges of the entire
old forest only at the exact parent separator, not at extra
vertices of unrelated members. -/
theorem JoinTree.leaf_support_cross_subset
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent) :
    ∀ ⦃eL eR : Set W⦄,
      eL ∈ (F leaf).edges →
      eR ∈ (⋃ j : {i : ι // i ≠ leaf}, (F j.1).edges) →
      eL ∩ eR ⊆
        (F leaf).carrier ∩ (F parent).carrier := by
  intro eL eR hEL hER x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hER
  have hxLeaf : x ∈ (F leaf).carrier :=
    (F leaf).edge_subset hEL hx.1
  have hxOther : x ∈ (F j.1).carrier :=
    (F j.1).edge_subset hj hx.2
  exact ⟨hxLeaf,
    J.mem_parent_of_mem_leaf_and_other
      hadj huniq j.2 hxLeaf hxOther⟩

/-- One inverse leaf deletion reconstructs the girth cutoff of the
WHOLE support-edge union, whether the permitted separator is
subsingleton or a complete support edge. -/
theorem JoinTree.girthGT_of_leaf_deletion
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    (hPair : PairwiseAllowed F)
    {leaf parent : ι}
    (hadj : J.tree.Adj leaf parent)
    (huniq : ∀ j : ι, J.tree.Adj leaf j → j = parent)
    (g : ℕ)
    (hRest : GirthGT
      (⋃ j : {i : ι // i ≠ leaf}, (F j.1).edges) g)
    (hLeaf : GirthGT (F leaf).edges g) :
    GirthGT (⋃ i : ι, (F i).edges) g := by
  let HRest : Set (Set W) :=
    ⋃ j : {i : ι // i ≠ leaf}, (F j.1).edges
  let HLeaf : Set (Set W) := (F leaf).edges
  have hCross :
      ∀ ⦃eL eR : Set W⦄, eL ∈ HLeaf → eR ∈ HRest →
        eL ∩ eR ⊆
          (F leaf).carrier ∩ (F parent).carrier :=
    J.leaf_support_cross_subset hadj huniq
  have hAllowed : AllowedIntersection (F leaf) (F parent) :=
    hPair hadj.ne
  have hGirth : GirthGT (HLeaf ∪ HRest) g := by
    rcases hAllowed with hSmall | ⟨S, hSLeaf, hSParent, hSInter⟩
    · exact girthGT_union_of_subsingleton_glue
        (S := (F leaf).carrier ∩ (F parent).carrier)
        hSmall hCross hLeaf hRest
    · have hSRest : S ∈ HRest := by
        apply Set.mem_iUnion.mpr
        exact ⟨⟨parent, hadj.ne.symm⟩, hSParent⟩
      have hCrossS :
          ∀ ⦃eL eR : Set W⦄, eL ∈ HLeaf → eR ∈ HRest →
            eL ∩ eR ⊆ S := by
        intro eL eR heL heR
        rw [← hSInter]
        exact hCross heL heR
      exact girthGT_union_of_edge_glue
        (separator := S)
        hSLeaf hSRest hCrossS hLeaf hRest
  rw [forestEdges_eq_leaf_union_rest F leaf]
  exact hGirth

/-- Any nontrivial finite forest has an actual removable leaf whose
complete intersection with the old union is the permitted
singleton-or-A-edge separator to its unique parent. The leaf-deleted
family remains a forest. -/
theorem ForestOfCopies.exists_permitted_leaf
    [Fintype ι] [Nontrivial ι]
    {F : ι → HypergraphPiece W}
    (hF : ForestOfCopies F) :
    ∃ leaf parent : ι,
      (∃ J : JoinTree F,
        J.tree.Adj leaf parent ∧
        (∀ j : ι, J.tree.Adj leaf j → j = parent)) ∧
      (F leaf).carrier ∩
        (⋃ j : {j : ι // j ≠ leaf}, (F j.1).carrier) =
          (F leaf).carrier ∩ (F parent).carrier ∧
      AllowedIntersection (F leaf) (F parent) ∧
      ForestOfCopies (erasePiece F leaf) := by
  classical
  obtain ⟨J⟩ := hF.joinTree_of_nonempty
  obtain ⟨leaf, parent, hadj, huniq, hOverlap⟩ :=
    J.exists_leaf_attachment
  refine ⟨leaf, parent, ⟨J, hadj, huniq⟩,
    hOverlap, hF.pairwiseAllowed hadj.ne, ?_⟩
  exact hF.erase_leaf J hadj huniq

end StructuralRamsey.Girth
