import Girth.ForestCompletionProperty
import Girth.ForestCompletionSeparatorRequests
import Girth.LinearityGirthTwo

/-!
# Two-edge forest completion already forces ambient linearity

For m >= 2, a forest-completion invariant testing EVERY one-edge
member implies that the tested support hypergraph is linear.
Adding designated pieces cannot repair a forbidden intersection
between the two distinct selected one-edge members: both survive
as members of the same completed forest.

This is a stronger assumption simplification for the active-subsystem
girth argument, independent of the direct forest increment.

Candidate source only. This declaration must pass exact-head Lean
compilation and #print axioms before it is a formal certificate.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- Completion of every tested pair of one-edge pieces implies
linearity of their underlying ambient support hypergraph.

The selected index type is a sum of two one-point types in
the SAME universe as the ambient vertex type. This avoids
requiring an arbitrary-universe lifting convention for Fin 2. -/
theorem linearEdgeSet_of_twoEdgeForestCompletion
    (H : Set (Set W))
    (tested designated : HypergraphPiece W → Prop)
    (m : ℕ) (hm : 2 ≤ m)
    (hComplete : ForestCompletionProperty tested designated m)
    (hTest : ∀ e : Set W, e ∈ H →
      tested (HypergraphPiece.oneEdge e)) :
    LinearEdgeSet H := by
  classical
  intro e f he hf hef
  let N : Type v := PUnit.{v+1} ⊕ PUnit.{v+1}
  let selected : N → HypergraphPiece W
    | .inl _ => HypergraphPiece.oneEdge e
    | .inr _ => HypergraphPiece.oneEdge f
  have hTestSelected : ∀ n : N, tested (selected n) := by
    intro n
    cases n with
    | inl _ => exact hTest e he
    | inr _ => exact hTest f hf
  have hCard : Fintype.card N ≤ m := by
    calc
      Fintype.card N = 2 := by simp [N]
      _ ≤ m := hm
  obtain ⟨K, finite, family, hWitness⟩ :=
    hComplete N selected hTestSelected hCard
  letI : Fintype K := finite
  obtain ⟨kE, hkE⟩ :=
    hWitness.2.1 (Sum.inl PUnit.unit)
  obtain ⟨kF, hkF⟩ :=
    hWitness.2.1 (Sum.inr PUnit.unit)
  have hE : family kE = HypergraphPiece.oneEdge e := by
    change family kE = HypergraphPiece.oneEdge e at hkE
    exact hkE
  have hF : family kF = HypergraphPiece.oneEdge f := by
    change family kF = HypergraphPiece.oneEdge f at hkF
    exact hkF
  have hDifferent : kE ≠ kF := by
    intro hSame
    apply hef
    have hPieces : HypergraphPiece.oneEdge e =
        HypergraphPiece.oneEdge f := by
      calc
        HypergraphPiece.oneEdge e = family kE := hE.symm
        _ = family kF := congrArg family hSame
        _ = HypergraphPiece.oneEdge f := hF
    simpa using congrArg HypergraphPiece.carrier hPieces
  rcases hWitness.1.pairwiseAllowed hDifferent with
      hSmall | ⟨g, hgE, hgF, _hIntersection⟩
  · simpa [hE, hF, HypergraphPiece.oneEdge] using hSmall
  · have hge : g = e := by
      rw [hE] at hgE
      change g ∈ ({e} : Set (Set W)) at hgE
      simpa using hgE
    have hgf : g = f := by
      rw [hF] at hgF
      change g ∈ ({f} : Set (Set W)) at hgF
      simpa using hgF
    exact (hef (hge.symm.trans hgf)).elim

end StructuralRamsey.Girth
