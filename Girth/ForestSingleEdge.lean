import Girth.Forest

/-! # One-edge members in forests

A one-A-copy member of the manuscript's support forest is represented by a
hypergraph piece whose unique support edge is its whole carrier.  The basic
intersection dichotomy below is the reason such a member can be deleted:
every other member meets it in at most one vertex, unless it contains the
whole edge.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

namespace HypergraphPiece

/-- A piece consisting of one support edge, with no additional carrier
vertices. -/
def IsOneEdge (F : HypergraphPiece W) : Prop :=
  F.edges = {F.carrier}

/-- If a one-edge piece has a non-singleton allowed intersection with another
piece, the latter contains the whole edge. -/
theorem carrier_subset_of_isOneEdge_of_allowed_not_subsingleton
    {F G : HypergraphPiece W}
    (hF : F.IsOneEdge)
    (hFG : AllowedIntersection F G)
    (hbig : ¬(F.carrier ∩ G.carrier).Subsingleton) :
    F.carrier ⊆ G.carrier := by
  rcases hFG with hsmall | ⟨e, heF, _heG, hinter⟩
  · exact (hbig hsmall).elim
  · have he : e = F.carrier := by
      rw [hF] at heF
      simpa using heF
    intro x hx
    have hxInter : x ∈ F.carrier ∩ G.carrier := by
      rw [hinter, he]
      exact hx
    exact hxInter.2

/-- Equivalently, an allowed intersection with a one-edge piece is either
subsingleton or the other carrier contains the whole edge. -/
theorem isOneEdge_allowed_dichotomy
    {F G : HypergraphPiece W}
    (hF : F.IsOneEdge)
    (hFG : AllowedIntersection F G) :
    (F.carrier ∩ G.carrier).Subsingleton ∨ F.carrier ⊆ G.carrier := by
  by_cases hsmall : (F.carrier ∩ G.carrier).Subsingleton
  · exact Or.inl hsmall
  · exact Or.inr
      (carrier_subset_of_isOneEdge_of_allowed_not_subsingleton
        hF hFG hsmall)

end HypergraphPiece

end StructuralRamsey.Girth
