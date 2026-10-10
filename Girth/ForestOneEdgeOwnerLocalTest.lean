import Girth.ForestMixedSetBound
import Girth.ForestCompletionSeparatorRequests

/-!
# One-edge exceptional owner: trivial old local forest requirement

The mixed-owner repair of the circulation direct forest increment uses a
one-edge outer owner for a selected edge of the local core.  Its selected
member and every incident separator request are the same one-edge piece.
Consequently the distinct old local request set has at most one element;
it satisfies the old q-forest bound WITHOUT a designated-copy owner.

The results below discharge the owner-dependent `tested` hypothesis of
`selectedForest_of_mixedRequestJoin` for these one-edge owners.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- A (possibly empty) subsingleton family is a forest of copies:
no two distinct labels can be involved in a forbidden intersection,
and any join tree has the running-intersection condition. -/
theorem forestOfCopies_of_subsingleton
    [Subsingleton I] (F : I → HypergraphPiece W) :
    ForestOfCopies F := by
  classical
  have hAllowed : PairwiseAllowed F := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  by_cases hNonempty : Nonempty I
  · let root : I := Classical.choice hNonempty
    let J : JoinTree F := {
      tree := SimpleGraph.starGraph root
      isTree := SimpleGraph.isTree_starGraph root
      running := by
        intro x
        haveI : Subsingleton {i : I | x ∈ (F i).carrier} := inferInstance
        exact SimpleGraph.Preconnected.of_subsingleton
    }
    exact ⟨hAllowed, Or.inr ⟨J⟩⟩
  · have hEmpty : IsEmpty I := ⟨fun i => hNonempty ⟨i⟩⟩
    exact ⟨hAllowed, Or.inl hEmpty⟩

/-- A local tested predicate admitting only a single one-edge piece
satisfies the bounded mixed forest property at EVERY cutoff. -/
theorem finiteMixedForestThrough_singleEdge
    (e : Set W) (q : ℕ) :
    FiniteMixedForestThrough
      (fun P : HypergraphPiece W => P = HypergraphPiece.oneEdge e)
      q := by
  classical
  intro s hTest _hBound
  haveI : Subsingleton {P : HypergraphPiece W // P ∈ s} := by
    constructor
    intro a b
    apply Subtype.ext
    exact (hTest a.1 a.2).trans (hTest b.1 b.2).symm
  exact forestOfCopies_of_subsingleton
    (fun P : {P : HypergraphPiece W // P ∈ s} => P.1)

end StructuralRamsey.Girth
