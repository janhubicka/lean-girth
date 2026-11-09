import Girth.CompactDiagramForest

open StructuralRamsey.Girth

#check JoinTree.compact_mem_carrier_of_mem_path
#check JoinTree.pairwiseAllowed_of_linkAllowed_of_linear
#check JoinTree.forestOfCopies_of_linkAllowed_of_linear
#check JoinTree.edge_occurrence_preconnected_of_linkAllowed_of_linear
#check forestOfCopies_iff_empty_or_linkAllowed_joinTree_of_linear

#print axioms StructuralRamsey.Girth.JoinTree.compact_mem_carrier_of_mem_path
#print axioms StructuralRamsey.Girth.JoinTree.pairwiseAllowed_of_linkAllowed_of_linear
#print axioms StructuralRamsey.Girth.JoinTree.forestOfCopies_of_linkAllowed_of_linear
#print axioms StructuralRamsey.Girth.JoinTree.edge_occurrence_preconnected_of_linkAllowed_of_linear
#print axioms StructuralRamsey.Girth.forestOfCopies_iff_empty_or_linkAllowed_joinTree_of_linear

/-! A finite regression for the essential ambient-linearity hypothesis.
Two distinct 3-edges on four points share two points.  Their union is the
centre of a three-member star.  Each link is a full allowed edge overlap,
and running intersection holds, but the two leaves have a forbidden overlap.
-/
namespace CompactDiagramForestRegression

def edge (b : Bool) : Set (Fin 4) :=
  if b then {x | x ≠ 2} else {x | x ≠ 3}

def leaf (b : Bool) : HypergraphPiece (Fin 4) where
  carrier := edge b
  edges := {edge b}
  edge_subset_carrier := by
    intro e he
    exact Set.mem_singleton_iff.mp he ▸ Set.Subset.refl _

def center : HypergraphPiece (Fin 4) where
  carrier := Set.univ
  edges := Set.range edge
  edge_subset_carrier := fun {_} _ => Set.subset_univ _

def family : Option Bool → HypergraphPiece (Fin 4)
  | none => center
  | some b => leaf b

def tree : JoinTree family where
  tree := SimpleGraph.starGraph none
  isTree := SimpleGraph.isTree_starGraph none
  running := fun x => starGraph_induce_preconnected_of_mem_center none
    (show x ∈ center.carrier from Set.mem_univ x)

theorem center_allowed (b : Bool) : AllowedIntersection center (leaf b) := by
  right
  exact ⟨edge b, ⟨b, rfl⟩, Set.mem_singleton _, Set.univ_inter _⟩

theorem links_allowed :
    ∀ ⦃i j⦄, tree.tree.Adj i j → AllowedIntersection (family i) (family j) := by
  intro i j hadj
  have h := SimpleGraph.starGraph_adj.mp hadj
  cases i with
  | none =>
    cases j with
    | none => exact (h.1 rfl).elim
    | some b => exact center_allowed b
  | some b =>
    cases j with
    | none => exact allowedIntersection_symm (center_allowed b)
    | some c => rcases h.2 with h | h <;> cases h

theorem leaves_not_allowed :
    ¬AllowedIntersection (family (some false)) (family (some true)) := by
  have hne : edge false ≠ edge true := by
    intro h
    have hx : (2 : Fin 4) ∈ edge false := by change (2 : Fin 4) ≠ 3; decide
    have hx' : (2 : Fin 4) ∉ edge true := by change ¬(2 : Fin 4) ≠ 2; decide
    exact hx' (h ▸ hx)
  rintro (hs | ⟨e, heL, heR, _⟩)
  · have h01 : (0 : Fin 4) = 1 := hs
      (by change (0 : Fin 4) ≠ 3 ∧ (0 : Fin 4) ≠ 2; decide)
      (by change (1 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2; decide)
    exact (by decide : (0 : Fin 4) ≠ 1) h01
  · apply hne
    exact (Set.mem_singleton_iff.mp heL).symm.trans (Set.mem_singleton_iff.mp heR)

theorem ambient_not_linear : ¬LinearEdgeSet (Set.range edge) := by
  intro hLinear
  have hForest := tree.forestOfCopies_of_linkAllowed_of_linear
    (Set.range edge) hLinear (by
      intro i e he
      cases i with
      | none => exact he
      | some b => exact ⟨b, (Set.mem_singleton_iff.mp he).symm⟩) links_allowed
  exact leaves_not_allowed (hForest.pairwiseAllowed (by decide))

theorem not_forest : ¬ForestOfCopies family := by
  intro h
  exact leaves_not_allowed (h.pairwiseAllowed (by decide))

#print axioms CompactDiagramForestRegression.leaves_not_allowed
#print axioms CompactDiagramForestRegression.ambient_not_linear
#print axioms CompactDiagramForestRegression.not_forest

end CompactDiagramForestRegression
