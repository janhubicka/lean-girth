import Girth.ForestNonEdgeOwner

/-!
# Valid one-separator replay for strong hypergraph pieces

A fresh strip over a picture is allowed to repeat privately over one
empty/vertex/support-edge separator.  This file isolates the pairwise-clean
part of that statement, using exactly the strongly-induced support-edge
condition needed to prevent a partial-edge overlap with an old B-copy.

It does not claim the invalid extension property for arbitrary
multi-contact records, nor global geometric compatibility with every
successor-tree shape map.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- If an old B-copy lies in the old picture and is strongly induced
with respect to every new support edge, a new B-copy attached to the
old picture along at most one vertex or exactly one support edge has an
allowed intersection with the old copy. -/
theorem allowedIntersection_of_oneSeparator_boundary
    (F G : HypergraphPiece W)
    (D : Set W)
    (hOld : F.carrier ⊆ D)
    (hBoundary :
      (G.carrier ∩ D).Subsingleton ∨
        ∃ e : Set W, e ∈ G.edges ∧ G.carrier ∩ D = e)
    (hStrong :
      ∀ e : Set W, e ∈ G.edges →
        ¬ (e ∩ F.carrier).Subsingleton → e ∈ F.edges) :
    AllowedIntersection F G := by
  rcases hBoundary with hSmall | ⟨e, heG, heBoundary⟩
  · left
    intro x hx y hy
    exact hSmall ⟨hx.2, hOld hx.1⟩ ⟨hy.2, hOld hy.1⟩
  · have hCapSub : F.carrier ∩ G.carrier ⊆ e := by
      intro x hx
      have hxD : x ∈ G.carrier ∩ D :=
        ⟨hx.2, hOld hx.1⟩
      rw [heBoundary] at hxD
      exact hxD
    by_cases hSmall : (F.carrier ∩ G.carrier).Subsingleton
    · exact Or.inl hSmall
    · have hEdgeCapBig : ¬ (e ∩ F.carrier).Subsingleton := by
        intro hEdgeSmall
        apply hSmall
        intro x hx y hy
        exact hEdgeSmall
          ⟨hCapSub hx, hx.1⟩
          ⟨hCapSub hy, hy.1⟩
      have heF : e ∈ F.edges := hStrong e heG hEdgeCapBig
      have hCapEq : F.carrier ∩ G.carrier = e := by
        apply Set.Subset.antisymm hCapSub
        intro x hx
        exact ⟨F.edge_subset heF hx, G.edge_subset heG hx⟩
      exact Or.inr ⟨e, heF, heG, hCapEq⟩

/-- The allowed-overlap property holds uniformly for every old member
when the single new strip is strongly supported across the old front. -/
theorem allowedIntersection_oldFamily_of_oneSeparator
    (Y : ι → HypergraphPiece W)
    (F : HypergraphPiece W)
    (D : Set W)
    (hOld : ∀ i : ι, (Y i).carrier ⊆ D)
    (hBoundary :
      (F.carrier ∩ D).Subsingleton ∨
        ∃ e : Set W, e ∈ F.edges ∧ F.carrier ∩ D = e)
    (hStrong :
      ∀ (i : ι) (e : Set W), e ∈ F.edges →
        ¬ (e ∩ (Y i).carrier).Subsingleton →
          e ∈ (Y i).edges) :
    ∀ i : ι, AllowedIntersection (Y i) F := by
  intro i
  exact allowedIntersection_of_oneSeparator_boundary
    (Y i) F D (hOld i) hBoundary (hStrong i)

/-- Repeated copies meeting *exactly* in the same permitted separator
are pairwise clean.  This captures the finite geometry of free fan-out,
provided the copies have genuinely private material outside the overlap. -/
theorem pairwiseAllowed_of_common_oneSeparator
    (P : ι → HypergraphPiece W)
    (κ : Set W)
    (hMeet :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (P i).carrier ∩ (P j).carrier = κ)
    (hSeparator :
      κ.Subsingleton ∨ ∀ i : ι, κ ∈ (P i).edges) :
    PairwiseAllowed P := by
  intro i j hij
  have hEq := hMeet hij
  rcases hSeparator with hSmall | hEdge
  · exact Or.inl (by simpa [hEq] using hSmall)
  · exact Or.inr ⟨κ, hEdge i, hEdge j, hEq⟩

end StructuralRamsey.Girth
