import Girth.CompactForestGluing

open StructuralRamsey.Girth

#check forestOfCopies_sumBridge_of_allowed_connectors_of_linear
#check forestOfCopies_sumPieces_of_subsingleton_union_overlap_of_linear
#check forestOfCopies_sumPieces_of_common_edge_anchors_of_linear

#print axioms StructuralRamsey.Girth.forestOfCopies_sumBridge_of_allowed_connectors_of_linear
#print axioms StructuralRamsey.Girth.forestOfCopies_sumPieces_of_subsingleton_union_overlap_of_linear
#print axioms StructuralRamsey.Girth.forestOfCopies_sumPieces_of_common_edge_anchors_of_linear

namespace CompactForestGluingRegression

def noEdges (S : Set ℕ) : HypergraphPiece ℕ where
  carrier := S
  edges := ∅
  edge_subset_carrier := fun {_} h => h.elim

def singletonFamily {W : Type} (P : HypergraphPiece W) : PUnit → HypergraphPiece W :=
  fun _ => P

theorem singletonFamily_forest {W : Type} (P : HypergraphPiece W) :
    ForestOfCopies (singletonFamily P) :=
  ⟨pairwiseAllowed_singlePiece P, Or.inr ⟨joinTree_singlePiece P⟩⟩

/-- Two genuine two-point charts meet at vertex 1. The result has only their
two existing labels: vertex 1 has not been inserted as a third member. -/
theorem singleton_link :
    ForestOfCopies (sumPieces
      (singletonFamily (noEdges {0, 1}))
      (singletonFamily (noEdges {1, 2}))) := by
  apply forestOfCopies_sumPieces_of_subsingleton_union_overlap_of_linear
    (singletonFamily_forest _) (singletonFamily_forest _) (∅ : Set (Set ℕ))
  · intro e f he
    exact he.elim
  · intro i e he
    exact he
  · intro j e he
    exact he
  · have hInter : ({0, 1} : Set ℕ) ∩ {1, 2} = {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    simpa only [singletonFamily, noEdges, Set.iUnion_const, hInter]
      using (Set.subsingleton_singleton (a := (1 : ℕ)))

theorem singleton_link_member_count : Fintype.card (PUnit ⊕ PUnit) = 2 := by decide

def edgeChart : HypergraphPiece Bool where
  carrier := Set.univ
  edges := {Set.univ}
  edge_subset_carrier := fun {_} _ => Set.subset_univ _

/-- A full physical edge can likewise be a link between two retained
one-edge charts, including repeated physical-edge occurrences. -/
theorem full_edge_link :
    ForestOfCopies (sumPieces (singletonFamily edgeChart) (singletonFamily edgeChart)) := by
  apply forestOfCopies_sumPieces_of_common_edge_anchors_of_linear
    (singletonFamily_forest _) (singletonFamily_forest _)
    ({Set.univ} : Set (Set Bool)) ?_
    (hEdgesF := fun _ => Set.Subset.refl _)
    (hEdgesG := fun _ => Set.Subset.refl _)
    PUnit.unit PUnit.unit Set.univ rfl rfl
    (Set.mem_singleton _) (Set.mem_singleton _) (Set.subset_univ _)
  intro e f he hf hne
  exact (hne ((Set.mem_singleton_iff.mp he).trans
    (Set.mem_singleton_iff.mp hf).symm)).elim

#print axioms CompactForestGluingRegression.singleton_link
#print axioms CompactForestGluingRegression.singleton_link_member_count
#print axioms CompactForestGluingRegression.full_edge_link

end CompactForestGluingRegression
