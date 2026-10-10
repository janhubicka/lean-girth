import Girth.ForestCompletionSeparatorRequests
import Girth.ForestOverlapTransfer

/-!
# Choose every full-standard separator edge inside the SMALL glued piece

The full standard picture can have private vertices not covered by
A-support edges. Therefore one must NOT assume vertex coverage of
each full standard picture to select separator edges.

Pairwise intersections of different FULL pictures equal the
intersections of their SMALL gluing support pieces, which ARE
vertex-covered by A-support edges. Select each separator edge
inside its small source piece, and use ambient support girth >2
to force exactness when the separator is nonsubsingleton.

Several oriented tree-neighbour requests may select the same
physical edge. No distinctness of connector labels is required.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- Every separator of the full standard pictures along a local
join tree has a covering physical A-support edge drawn from the
corresponding small gluing copy. At a nonsubsingleton separator
the chosen edge is EXACTLY that separator. -/
theorem exists_smallSupport_separatorEdges
    {small full : Q → HypergraphPiece W}
    (hSmallForest : ForestOfCopies small)
    (J : JoinTree small)
    (hOverlap :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (full q).carrier ∩ (full r).carrier =
          (small q).carrier ∩ (small r).carrier)
    (hSmallEdges :
      ∀ q : Q, (small q).edges ⊆ (full q).edges)
    (hSmallNonempty :
      ∀ q : Q, (small q).edges.Nonempty)
    (hSmallVertexCovered :
      ∀ q (x : W), x ∈ (small q).carrier →
        ∃ e : Set W, e ∈ (small q).edges ∧ x ∈ e)
    {H : Set (Set W)}
    (hFullEdgesAmbient :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full q).edges → e ∈ H)
    (hGirth : GirthGT H 2) :
    ∃ edge : (q : Q) → J.tree.neighborSet q → Set W,
      ∀ q (r : J.tree.neighborSet q),
        edge q r ∈ (small q).edges ∧
        edge q r ⊆ (full q).carrier ∧
        (full q).carrier ∩ (full r.1).carrier ⊆ edge q r ∧
        (¬((full q).carrier ∩ (full r.1).carrier).Subsingleton →
          edge q r =
            (full q).carrier ∩ (full r.1).carrier) := by
  classical
  have hAmbientSmall :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (small q).edges → e ∈ H := by
    intro q e he
    exact hFullEdgesAmbient q (hSmallEdges q he)
  have hChoose (q : Q) (r : J.tree.neighborSet q) :
      ∃ e : Set W, e ∈ (small q).edges ∧
        (small q).carrier ∩ (small r.1).carrier ⊆ e :=
    exists_support_edge_covering_separator
      hSmallForest.pairwiseAllowed
      hSmallNonempty hSmallVertexCovered r.2.ne
  let edge (q : Q) (r : J.tree.neighborSet q) : Set W :=
    Classical.choose (hChoose q r)
  refine ⟨edge, ?_⟩
  intro q r
  have hs := Classical.choose_spec (hChoose q r)
  refine ⟨hs.1, (full q).edge_subset (hSmallEdges q hs.1), ?_, ?_⟩
  · rw [hOverlap r.2.ne]
    exact hs.2
  · intro hBig
    have hBigSmall :
        ¬((small q).carrier ∩ (small r.1).carrier).Subsingleton := by
      rw [← hOverlap r.2.ne]
      exact hBig
    have hExact :=
      separator_edge_exact_of_ambient_girth
        hSmallForest.pairwiseAllowed hAmbientSmall hGirth
        r.2.ne hs.1 hs.2 hBigSmall
    calc
      edge q r = (small q).carrier ∩
          (small r.1).carrier := hExact
      _ = (full q).carrier ∩
          (full r.1).carrier := (hOverlap r.2.ne).symm

end StructuralRamsey.Girth
