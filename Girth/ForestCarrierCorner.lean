import Girth.ForestAttach

/-! # Carrier obstruction for incomparable boundary separators

This file isolates the second finite combinatorial step in the successor-tree
forest proof.  If two incomparable boundary intersections of one piece are not
jointly contained in any support edge of that piece, then no pairwise-allowed
second piece can contain both boundaries.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- If two boundary subsets of F are incomparable and no support edge of F
contains both, then a second piece containing both cannot have an allowed
intersection with F.

In the successor proof the two subsets are the intersections of the moving
B-copy with two frozen old copies. -/
theorem not_allowedIntersection_of_contains_incomparable_uncovered
    (F G H F' : HypergraphPiece W)
    (hNotST :
      ¬(F.carrier ∩ G.carrier ⊆
        F.carrier ∩ H.carrier))
    (hNotTS :
      ¬(F.carrier ∩ H.carrier ⊆
        F.carrier ∩ G.carrier))
    (hNoEdge :
      ∀ ⦃e : Set W⦄, e ∈ F.edges →
        ¬((F.carrier ∩ G.carrier) ∪
            (F.carrier ∩ H.carrier) ⊆ e))
    (hContainG :
      F.carrier ∩ G.carrier ⊆ F'.carrier)
    (hContainH :
      F.carrier ∩ H.carrier ⊆ F'.carrier) :
    ¬ AllowedIntersection F F' := by
  intro hAllowed
  obtain ⟨x, hxFG, hxNotFH⟩ :=
    Set.not_subset.mp hNotST
  obtain ⟨y, hyFH, hyNotFG⟩ :=
    Set.not_subset.mp hNotTS
  have hxy : x ≠ y := by
    intro hxy
    apply hxNotFH
    simpa [hxy] using hyFH
  have hxFF' :
      x ∈ F.carrier ∩ F'.carrier :=
    ⟨hxFG.1, hContainG hxFG⟩
  have hyFF' :
      y ∈ F.carrier ∩ F'.carrier :=
    ⟨hyFH.1, hContainH hyFH⟩
  rcases hAllowed with hSmall | ⟨e, heF, _heF', hEq⟩
  · exact hxy (hSmall hxFF' hyFF')
  · apply hNoEdge heF
    intro z hz
    rcases hz with hzG | hzH
    · have hzInter :
          z ∈ F.carrier ∩ F'.carrier :=
        ⟨hzG.1, hContainG hzG⟩
      rw [hEq] at hzInter
      exact hzInter
    · have hzInter :
          z ∈ F.carrier ∩ F'.carrier :=
        ⟨hzH.1, hContainH hzH⟩
      rw [hEq] at hzInter
      exact hzInter

/-- Positive formulation: under incomparable boundaries, every pairwise-allowed
piece which contains both forces a support edge of F covering their union. -/
theorem exists_edge_cover_of_allowed_contains_incomparable
    (F G H F' : HypergraphPiece W)
    (hNotST :
      ¬(F.carrier ∩ G.carrier ⊆
        F.carrier ∩ H.carrier))
    (hNotTS :
      ¬(F.carrier ∩ H.carrier ⊆
        F.carrier ∩ G.carrier))
    (hAllowed : AllowedIntersection F F')
    (hContainG :
      F.carrier ∩ G.carrier ⊆ F'.carrier)
    (hContainH :
      F.carrier ∩ H.carrier ⊆ F'.carrier) :
    ∃ e : Set W, e ∈ F.edges ∧
      (F.carrier ∩ G.carrier) ∪
        (F.carrier ∩ H.carrier) ⊆ e := by
  by_contra hNo
  push_neg at hNo
  exact
    (not_allowedIntersection_of_contains_incomparable_uncovered
      F G H F' hNotST hNotTS
      (by
        intro e heF
        exact hNo e heF)
      hContainG hContainH) hAllowed


/-- A set of support edges is linear when two distinct edges meet
subsingletonly. -/
def LinearEdgeSet (E : Set (Set W)) : Prop :=
  ∀ ⦃e f : Set W⦄,
    e ∈ E → f ∈ E → e ≠ f →
      (e ∩ f).Subsingleton

/-- The A-carrier half of the successor corner lemma.  Two edges in one
linear ambient support family cannot both contain two incomparable boundary
sets unless they are the same edge. -/
theorem edge_eq_of_contains_incomparable
    (E : Set (Set W))
    (hLinear : LinearEdgeSet E)
    (S T e f : Set W)
    (hNotST : ¬ S ⊆ T)
    (hNotTS : ¬ T ⊆ S)
    (he : e ∈ E) (hf : f ∈ E)
    (hSe : S ⊆ e) (hTe : T ⊆ e)
    (hSf : S ⊆ f) (hTf : T ⊆ f) :
    e = f := by
  by_contra hef
  obtain ⟨x, hxS, hxNotT⟩ :=
    Set.not_subset.mp hNotST
  obtain ⟨y, hyT, hyNotS⟩ :=
    Set.not_subset.mp hNotTS
  have hxy : x ≠ y := by
    intro hxy
    apply hxNotT
    simpa [hxy] using hyT
  have hsmall : (e ∩ f).Subsingleton :=
    hLinear he hf hef
  apply hxy
  exact hsmall
    ⟨hSe hxS, hSf hxS⟩
    ⟨hTe hyT, hTf hyT⟩

end StructuralRamsey.Girth
