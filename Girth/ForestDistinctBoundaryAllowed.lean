import Girth.ForestCarrierCorner
import Girth.Berge

/-!
# Pairwise allowed intersections in the all-distinct forest increment

In the final case of the direct forest increment (manuscript
Lemma forestincrement), every selected member has a DIFFERENT full
standard-picture owner. Therefore two selected members can meet only
inside the local hypergraph S.

Each individual selected member meets S in either at most one vertex
or one full local support edge which genuinely belongs to that member.
If S is linear, two members sharing at least two vertices must have
the same boundary support edge. Hence their intersection is exactly
that common edge, and every pair of members is allowed.

This is the full pairwise-intersection half of the all-distinct case.
The separate remaining obligation is to construct the running-
intersection join tree from the acyclic boundary incidence graph.
Acyclicity follows from local girth >q for at most q selected
boundary edges, but that construction is not asserted here.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- An actual selected member meets the local core in at most one
vertex or exactly one whole local support edge which it contains.
Empty boundaries are included in the subsingleton case. -/
def SmallOrWholeEdgeBoundary
    (K : Set (Set W)) (S : Set W)
    (F : HypergraphPiece W) : Prop :=
  (F.carrier ∩ S).Subsingleton ∨
    ∃ e : Set W, e ∈ K ∧ e ∈ F.edges ∧ F.carrier ∩ S = e

/-- Under pairwise owner separation, local edge linearity forces
ALL intersections of distinct selected members to be allowed.
No join-tree or family-cardinality assumption enters this claim. -/
theorem pairwiseAllowed_of_distinctOwner_boundaries
    (F : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (hLinear : LinearEdgeSet K)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (F i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
       (F i).carrier ∩ (F j).carrier ⊆ S) :
    PairwiseAllowed F := by
  intro i j hij
  by_cases hSmall :
      ((F i).carrier ∩ (F j).carrier).Subsingleton
  · exact Or.inl hSmall
  · obtain ⟨x, hx, y, hy, hxy⟩ :=
      Set.not_subsingleton_iff.mp hSmall
    have hxS : x ∈ S := hCross hij hx
    have hyS : y ∈ S := hCross hij hy
    have hNotI : ¬((F i).carrier ∩ S).Subsingleton := by
      intro hs
      exact hxy (hs ⟨hx.1, hxS⟩ ⟨hy.1, hyS⟩)
    have hNotJ : ¬((F j).carrier ∩ S).Subsingleton := by
      intro hs
      exact hxy (hs ⟨hx.2, hxS⟩ ⟨hy.2, hyS⟩)
    obtain ⟨e, heK, heF, heBoundary⟩ :=
      (hBoundary i).resolve_left hNotI
    obtain ⟨f, hfK, hfF, hfBoundary⟩ :=
      (hBoundary j).resolve_left hNotJ
    have hxE : x ∈ e := by
      rw [← heBoundary]
      exact ⟨hx.1, hxS⟩
    have hyE : y ∈ e := by
      rw [← heBoundary]
      exact ⟨hy.1, hyS⟩
    have hxF : x ∈ f := by
      rw [← hfBoundary]
      exact ⟨hx.2, hxS⟩
    have hyF : y ∈ f := by
      rw [← hfBoundary]
      exact ⟨hy.2, hyS⟩
    have hEq : e = f := by
      by_contra hef
      have hSub : (e ∩ f).Subsingleton :=
        hLinear heK hfK hef
      exact hxy (hSub ⟨hxE, hxF⟩ ⟨hyE, hyF⟩)
    have heG : e ∈ (F j).edges := by
      rw [hEq]
      exact hfF
    refine Or.inr ⟨e, heF, heG, ?_⟩
    apply Set.Subset.antisymm
    · intro z hz
      rw [← heBoundary]
      exact ⟨hz.1, hCross hij hz⟩
    · intro z hz
      exact ⟨(F i).edge_subset heF hz,
        (F j).edge_subset heG hz⟩

/-- No separate linearity hypothesis is required: local Berge girth
strictly above two gives exactly the needed pairwise intersection
bound for all selected full-standard members with distinct owners. -/
theorem pairwiseAllowed_of_distinctOwner_girthTwo
    (F : I → HypergraphPiece W)
    (S : Set W) (K : Set (Set W))
    (hGirth : GirthGT K 2)
    (hBoundary : ∀ i, SmallOrWholeEdgeBoundary K S (F i))
    (hCross : ∀ ⦃i j : I⦄, i ≠ j →
       (F i).carrier ∩ (F j).carrier ⊆ S) :
    PairwiseAllowed F := by
  have hLinear : LinearEdgeSet K := by
    intro e f he hf hne
    exact pairwise_subsingleton_of_girthGT_two
      hGirth he hf hne
  exact pairwiseAllowed_of_distinctOwner_boundaries
    F S K hLinear hBoundary hCross

end StructuralRamsey.Girth
