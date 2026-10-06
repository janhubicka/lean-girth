import Girth.ForestGirth

/-! # Allowed intersections across a forest separator

These lemmas isolate the cross-piece intersection argument used in the
manuscript's join-tree lifting lemma.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- If a cross intersection is contained in a subsingleton separator, it is
automatically an allowed intersection. -/
theorem allowedIntersection_of_inter_subset_subsingleton
    {F G : HypergraphPiece W}
    {S : Set W}
    (hS : S.Subsingleton)
    (hCross : F.carrier ∩ G.carrier ⊆ S) :
    AllowedIntersection F G := by
  left
  intro x hx y hy
  exact hS (hCross hx) (hCross hy)

/-- If two members meet only inside a separator edge and each local forest
contains that separator as a one-edge member, then the two members have an
allowed cross intersection.  A non-singleton cross intersection forces the
whole separator edge into both members. -/
theorem allowedIntersection_across_edge_separator
    {F G : HypergraphPiece W}
    {e : Set W}
    (hFE : AllowedIntersection F (oneEdgePiece e))
    (hGE : AllowedIntersection G (oneEdgePiece e))
    (hCross : F.carrier ∩ G.carrier ⊆ e) :
    AllowedIntersection F G := by
  by_cases hSmall : (F.carrier ∩ G.carrier).Subsingleton
  · exact Or.inl hSmall
  · have hFNon :
        ¬ (F.carrier ∩ e).Subsingleton := by
      intro h
      apply hSmall
      intro x hx y hy
      apply h
      · exact ⟨hx.1, hCross hx⟩
      · exact ⟨hy.1, hCross hy⟩
    have hGNon :
        ¬ (G.carrier ∩ e).Subsingleton := by
      intro h
      apply hSmall
      intro x hx y hy
      apply h
      · exact ⟨hx.2, hCross hx⟩
      · exact ⟨hy.2, hCross hy⟩
    rcases hFE with hFSmall | ⟨f, hfF, hfE, hFint⟩
    · exact (hFNon (by simpa [oneEdgePiece] using hFSmall)).elim
    · have hfe : f = e := by
        simpa [oneEdgePiece] using hfE
      subst f
      rcases hGE with hGSmall | ⟨g, hgG, hgE, hGint⟩
      · exact (hGNon (by simpa [oneEdgePiece] using hGSmall)).elim
      · have hge : g = e := by
          simpa [oneEdgePiece] using hgE
        subst g
        have hFint' : F.carrier ∩ e = e := by
          simpa [oneEdgePiece] using hFint
        have hGint' : G.carrier ∩ e = e := by
          simpa [oneEdgePiece] using hGint
        right
        refine ⟨e, hfF, hgG, ?_⟩
        apply Set.Subset.antisymm hCross
        intro x hx
        have hxF : x ∈ F.carrier := by
          have : x ∈ F.carrier ∩ e := by
            rw [hFint']
            exact hx
          exact this.1
        have hxG : x ∈ G.carrier := by
          have : x ∈ G.carrier ∩ e := by
            rw [hGint']
            exact hx
          exact this.1
        exact ⟨hxF, hxG⟩

end StructuralRamsey.Girth
