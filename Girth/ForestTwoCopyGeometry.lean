import Girth.ForestFreshCarrier
import Girth.ForestReplayObstruction
import Mathlib.Tactic

/-!
# The complete finite geometric contradiction for two moving copies

For a minimally nonforest family with old front Y and moving B-piece F,
the verified fresh-carrier lemma gives incomparable boundary separators
and one of two alternatives: a fresh A-edge covering both separators,
or the entire B-piece as carrier.

If a second moving B-piece F' contains the same old-front separators,
then either its fresh A-edge must coincide with the first carrier
(violating carrier separation in a globally linear A-support), or the
two B-pieces have an impermissible intersection. Thus no bad profile
can survive a *carrier-faithful* two-copy test.

This is finite geometry, not the existence of a universal history
reservoir, of tests under every shape map, or of Ramsey arrows.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Incomparable subsets of a common carrier have a union containing
two distinct vertices. -/
private theorem incomparable_union_not_subsingleton
    (S T : Set W)
    (hST : ¬ S ⊆ T) (hTS : ¬ T ⊆ S) :
    ¬ (S ∪ T).Subsingleton := by
  obtain ⟨x, hxS, hxNotT⟩ := Set.not_subset.mp hST
  obtain ⟨y, hyT, hyNotS⟩ := Set.not_subset.mp hTS
  have hxy : x ≠ y := by
    intro h
    exact hxNotT (by simpa [h] using hyT)
  intro hSmall
  exact hxy (hSmall (Or.inl hxS) (Or.inr hyT))

/-- Two linear support edges covering the union of incomparable boundary
separators must be the very same A-edge. -/
theorem edge_carriers_equal_of_incomparable_contacts
    (E : Set (Set W))
    (hLinear : LinearEdgeSet E)
    (S T : Set W)
    (hST : ¬ S ⊆ T)
    (hTS : ¬ T ⊆ S)
    {e e' : Set W}
    (he : e ∈ E) (he' : e' ∈ E)
    (hCover : S ∪ T ⊆ e)
    (hCover' : S ∪ T ⊆ e') :
    e = e' := by
  have hBig := incomparable_union_not_subsingleton S T hST hTS
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ S ∪ T, ∃ y ∈ S ∪ T, x ≠ y := by
    by_contra h
    apply hBig
    intro x hx y hy
    by_contra hxy
    exact h ⟨x, hx, y, hy, hxy⟩
  exact linearEdge_eq_of_two_shared_vertices E hLinear
    he he' hxy (hCover hx) (hCover' hx)
    (hCover hy) (hCover' hy)

/-- The assembled finite-carrier obstruction. Every condition here is
geometric and decidable on a finite labelled support picture. The
application-level missing interface is to realize the two moving
copies with the same old front and the specified distinct carriers. -/
theorem badForest_twoCopy_geometry_contradiction
    [Fintype ι] [Nonempty ι] [Finite W]
    (E : Set (Set W))
    (hLinear : LinearEdgeSet E)
    (Y : ι → HypergraphPiece W)
    (hY : ForestOfCopies Y)
    (F F' : HypergraphPiece W)
    (hCross : ∀ i : ι, AllowedIntersection F (Y i))
    (hBad :
      ¬ ForestOfCopies
        (sumPieces Y (fun _ : PUnit.{v+1} => F)))
    (hEdgeBig :
      ∀ ⦃e : Set W⦄, e ∈ F.edges → ¬ e.Subsingleton)
    (hAnti : EdgeAntichain F)
    (hFreshWhole :
      ∀ i : ι, ¬ F.carrier ⊆ (Y i).carrier)
    (hSameFront :
      ∀ i : ι, F.carrier ∩ (Y i).carrier ⊆ F'.carrier)
    (hEdgesF : F.edges ⊆ E)
    (hEdgesF' : F'.edges ⊆ E)
    (hFreshA :
      ∀ (i j : ι) (e : Set W),
        e ∈ F.edges →
        (F.carrier ∩ (Y i).carrier) ∪
          (F.carrier ∩ (Y j).carrier) ⊆ e →
        ∃ e' : Set W,
          e' ∈ F'.edges ∧
          (F.carrier ∩ (Y i).carrier) ∪
            (F.carrier ∩ (Y j).carrier) ⊆ e' ∧
          e' ≠ e)
    (hPairwiseMoving : AllowedIntersection F F') :
    False := by
  obtain ⟨i, j, hIJ, hJI, hCarrier⟩ :=
    exists_incomparable_fresh_carrier
      hY F hCross hBad hEdgeBig hAnti hFreshWhole
  rcases hCarrier with hA | hB
  · obtain ⟨e, heF, hCover, _⟩ := hA
    obtain ⟨e', heF', hCover', hDiff⟩ :=
      hFreshA i j e heF hCover
    have hEq :=
      edge_carriers_equal_of_incomparable_contacts
        E hLinear
        (F.carrier ∩ (Y i).carrier)
        (F.carrier ∩ (Y j).carrier)
        hIJ hJI
        (hEdgesF heF) (hEdgesF' heF')
        hCover hCover'
    exact hDiff hEq.symm
  · have hNoCover := hB.1
    have hNotAllowed :=
      not_allowedIntersection_of_contains_incomparable_uncovered
        F (Y i) (Y j) F' hIJ hJI hNoCover
        (hSameFront i) (hSameFront j)
    exact hNotAllowed hPairwiseMoving

end StructuralRamsey.Girth
