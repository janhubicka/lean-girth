import Girth.TrainColouredOwnerWholeEdgeIntersection
import Girth.Forest
import Girth.TrainColouredOwnerExactColourTransfer

/-!
# Numbered Track 1: full selected support pieces after owner splitting

The carrier is the exact lifted selected vertex range, including isolated
marked vertices with their shared bottom tags. The selected edges are
exactly the split images of the actual source edges.

This is an elementary adapter to the existing checked owner-splitting
geometry: old empty/singleton intersections stay small, and an old
whole common physical A-edge becomes exactly the same whole split
A-edge belonging to both lifted selected copies.

Unlike an arbitrary collection of abstract carriers, the resulting
pieces satisfy the actual edge-membership requirement in
AllowedIntersection. No Ramsey arrow is assumed or established here.

STAGED DRAFT, not yet Lean-compiled.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I W Choice : Type v}
variable {H : ColouredEdgeOwnerSplit V I}

namespace ColouredOwnerSelectedCopy

/-- The actual selected B-support piece, with precisely its source
support edges transported to the split ambient hypergraph. -/
noncomputable def selectedLiftSupportPiece
    (S : ColouredOwnerSelectedCopy (W := W) H) :
    HypergraphPiece H.Vertex where
  carrier := Set.range S.lift
  edges := {e | ∃ a : S.SourceEdge,
    e = H.splitEdge (S.physicalEdge a)}
  edge_subset_carrier := by
    intro e he
    obtain ⟨a, rfl⟩ := he
    exact S.split_selected_edge_subset_copy a

/-- Two selected lifted supports have an allowed physical intersection
whenever their old carriers met in at most one point or inside an
actual source A-edge selected in BOTH copies. -/
theorem selectedLiftSupport_allowed
    (S T : ColouredOwnerSelectedCopy (W := W) H)
    (hOld :
      (Set.range S.embedding ∩ Set.range T.embedding).Subsingleton ∨
        ∃ f : H.OldEdge,
          Set.range S.embedding ∩ Set.range T.embedding ⊆ f.1 ∧
          f ∈ Set.range S.physicalEdge ∧
          f ∈ Set.range T.physicalEdge) :
    AllowedIntersection S.selectedLiftSupportPiece T.selectedLiftSupportPiece := by
  rcases hOld with hSmall | ⟨f, hInside, hS, hT⟩
  · exact Or.inl (S.lifted_pair_intersection_subsingleton T hSmall)
  · right
    refine ⟨H.splitEdge f, ?_, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hS
      exact ⟨a, (congrArg H.splitEdge ha).symm⟩
    · obtain ⟨a, ha⟩ := hT
      exact ⟨a, (congrArg H.splitEdge ha).symm⟩
    · exact S.lifted_intersection_eq_splitEdge T f hInside hS hT

/-- The whole selected lifted B-family has permitted pair intersections
without postulating an intersection condition on its output images. -/
theorem selectedLiftSupport_pairwiseAllowed
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hOld : ∀ ⦃i j : Choice⦄, i ≠ j →
      (Set.range (selected i).embedding ∩
        Set.range (selected j).embedding).Subsingleton ∨
        ∃ f : H.OldEdge,
          Set.range (selected i).embedding ∩
            Set.range (selected j).embedding ⊆ f.1 ∧
          f ∈ Set.range (selected i).physicalEdge ∧
          f ∈ Set.range (selected j).physicalEdge) :
    PairwiseAllowed
      (fun i : Choice => (selected i).selectedLiftSupportPiece) := by
  intro i j hij
  exact selectedLiftSupport_allowed (selected i) (selected j) (hOld hij)

#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.selectedLiftSupport_allowed
#print axioms StructuralRamsey.Girth.ColouredOwnerSelectedCopy.selectedLiftSupport_pairwiseAllowed

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
