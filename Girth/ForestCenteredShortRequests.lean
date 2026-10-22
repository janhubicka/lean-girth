import Girth.ForestStar
import Girth.ForestCompletionSeparatorRequests

/-!
# Forest of one owner and short auxiliary requests

The strengthened pure-to-mixed covered-family lemma has two local cases.
If the owning B-piece itself was selected, the local forest is a star
centered at that owner. Leaves may be actual one-edge support pieces,
or *edge-free* singleton requests, even at isolated vertices.

The theorem is independent of local girth beyond support linearity.
It allows repeated leaf occurrences with identical support edges or
identical singleton carriers; the centre is the unique distinguished
whole owner and is never duplicated.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

def centerWithShortLeaves
    (F : HypergraphPiece W)
    (leaf : I → HypergraphPiece W) :
    Option I → HypergraphPiece W
  | none => F
  | some i => leaf i

/-- The selected whole owner plus arbitrarily many short requests form
a forest if every request is contained in the owner, and every
non-singleton request is one actual support edge of that owner.
No vertex-support assumption for singleton requests is used. -/
theorem forest_centerWithShortLeaves
    (F : HypergraphPiece W)
    (leaf : I → HypergraphPiece W)
    (hSub : ∀ i, (leaf i).carrier ⊆ F.carrier)
    (hShort : ∀ i, (leaf i).carrier.Subsingleton ∨
      ∃ e : Set W, e ∈ F.edges ∧
        leaf i = HypergraphPiece.oneEdge e)
    (hLinear : ∀ ⦃e f : Set W⦄,
      e ∈ F.edges → f ∈ F.edges → e ≠ f →
        (e ∩ f).Subsingleton) :
    ForestOfCopies (centerWithShortLeaves F leaf) := by
  classical
  have hCenter (i : I) : AllowedIntersection F (leaf i) := by
    rcases hShort i with hSmall | ⟨e, he, hi⟩
    · left
      intro x hx y hy
      exact hSmall hx.2 hy.2
    · right
      refine ⟨e, he, ?_, ?_⟩
      · simp [hi, HypergraphPiece.oneEdge]
      · rw [hi]
        change F.carrier ∩ e = e
        exact Set.inter_eq_right.mpr (F.edge_subset he)
  have hLeaves (i j : I) :
      AllowedIntersection (leaf i) (leaf j) := by
    rcases hShort i with hSmall | ⟨e, he, hi⟩
    · left
      intro x hx y hy
      exact hSmall hx.1 hy.1
    rcases hShort j with hSmall | ⟨f, hf, hj⟩
    · left
      intro x hx y hy
      exact hSmall hx.2 hy.2
    by_cases hef : e = f
    · subst f
      right
      refine ⟨e, ?_, ?_, ?_⟩
      · simp [hi, HypergraphPiece.oneEdge]
      · simp [hj, HypergraphPiece.oneEdge]
      · simp [hi, hj, HypergraphPiece.oneEdge]
    · left
      simpa [hi, hj, HypergraphPiece.oneEdge] using
        hLinear he hf hef
  have hPair : PairwiseAllowed (centerWithShortLeaves F leaf) := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact hCenter j
    | some i =>
        cases j with
        | none => exact allowedIntersection_symm (hCenter i)
        | some j => exact hLeaves i j
  refine ⟨hPair, Or.inr ⟨?_⟩⟩
  refine
    { tree := SimpleGraph.starGraph (none : Option I)
      isTree := SimpleGraph.isTree_starGraph (none : Option I)
      running := ?_ }
  intro x
  by_cases hx : x ∈ F.carrier
  · have hcenter :
        (none : Option I) ∈
          {k : Option I |
            x ∈ (centerWithShortLeaves F leaf k).carrier} := by
      exact hx
    exact starGraph_induce_preconnected_of_mem_center
      (none : Option I) hcenter
  · intro a b
    exfalso
    apply hx
    cases hi : a.1 with
    | none =>
        simpa [centerWithShortLeaves, hi] using a.2
    | some i =>
        have hxi : x ∈ (leaf i).carrier := by
          simpa [centerWithShortLeaves, hi] using a.2
        exact hSub i hxi

end StructuralRamsey.Girth
