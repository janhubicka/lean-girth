import Girth.ForestStar
import Girth.ForestCompletionSeparatorRequests
import Girth.ForestUsedOwnerLocalForest

set_option autoImplicit false
set_option Elab.async false

/-!
# Repeated labels of one and the same physical edge

The genuine finite-set forest condition cannot generally be applied
to a list which repeats the same multi-edge designated support.
But a single one-edge support may be repeated under arbitrarily
many different labels. A star join tree has the running-intersection
property because all those labels have the identical carrier.

This is the elementary single-edge-target branch of the finite
forest-to-system-girth conversion; it needs no two-distinct-edge
hypothesis, no injective support-index family, and no Ramsey input.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- Any (possibly empty) family all of whose members are the same
one-edge piece is a forest, even if its labels are not injective. -/
theorem forestOfCopies_constant_oneEdge
    (e : Set W) (I : Type v) :
    ForestOfCopies (fun _ : I => HypergraphPiece.oneEdge e) := by
  classical
  have hAllowed : PairwiseAllowed
      (fun _ : I => HypergraphPiece.oneEdge e) := by
    intro i j _hDifferent
    right
    refine ⟨e, ?_, ?_, ?_⟩
    · exact Set.mem_singleton e
    · exact Set.mem_singleton e
    · exact Set.inter_self e
  by_cases hIndex : Nonempty I
  · let root : I := Classical.choice hIndex
    refine ⟨hAllowed, Or.inr ⟨{
      tree := SimpleGraph.starGraph root
      isTree := SimpleGraph.isTree_starGraph root
      running := ?_ }⟩⟩
    intro x
    by_cases hx : x ∈ e
    · have hRoot :
          root ∈ {i : I | x ∈ (HypergraphPiece.oneEdge e).carrier} := by
        simpa only [HypergraphPiece.oneEdge_carrier] using hx
      exact starGraph_induce_preconnected_of_mem_center root hRoot
    · haveI : Subsingleton
          {i : I | x ∈ (HypergraphPiece.oneEdge e).carrier} := by
        constructor
        intro a b
        exact (hx (by simpa only [HypergraphPiece.oneEdge_carrier] using a.2)).elim
      exact SimpleGraph.Preconnected.of_subsingleton
  · have hEmpty : IsEmpty I := ⟨fun i => hIndex ⟨i⟩⟩
    exact ⟨hAllowed, Or.inl hEmpty⟩

/-- When every selected label of a local witness really has the
same physical one-edge support, the requested LocalForestThrough
holds at every cutoff, including q=2. No deduplication is required. -/
theorem localForestThrough_of_constant_oneEdge
    (F : I → HypergraphPiece W) (e : Set W)
    (hConstant : ∀ i : I, F i = HypergraphPiece.oneEdge e)
    (q : ℕ) :
    LocalForestThrough F q := by
  intro Q _ idx _hCard
  have hEq : (fun j : Q => F (idx j)) =
      (fun _ : Q => HypergraphPiece.oneEdge e) := by
    funext j
    exact hConstant (idx j)
  rw [hEq]
  exact forestOfCopies_constant_oneEdge e Q

end StructuralRamsey.Girth
