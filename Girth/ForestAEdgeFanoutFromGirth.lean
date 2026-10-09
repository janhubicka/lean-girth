import Girth.ForestSafeFanoutInvariants
import Girth.Berge

/-!
# Safe A-edge fanout directly from the ambient girth invariant

The complete-A-edge fanout theorem takes linearity of the old
B-owner's intrinsic support as an explicit hypothesis. In the
circulation/successor applications, this is not an extra assumption:
ambient A-support girth greater than a cutoff g >= 2 already implies
linearity of every subfamily of support edges.

This file discharges the owner-linearity premise from the old
ambient girth invariant, leaving precisely the hypotheses of
a picture step: old designated forest, old support girth,
a designated owner, and one complete A-edge of that owner.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I : Type v}

/-- The owner B-piece's support is linear whenever its edges belong
to an ambient support hypergraph with no Berge 2-cycle. -/
theorem ownerLinear_of_ambientGirthTwo
    (H : Set (Set W)) (P : HypergraphPiece W)
    (hSubset : P.edges ⊆ H)
    (hGirth : GirthGT H 2) :
    LinearEdgeSet P.edges := by
  intro e f he hf hne
  exact (pairwise_subsingleton_of_girthGT_two hGirth)
    (hSubset he) (hSubset hf) hne

/-- No separate linearity hypothesis is needed once ambient girth
is at least two. One full owner A-edge can be used for a private
B-copy clone while preserving BOTH the B-copy forest invariant
and the original ambient Berge-girth cutoff. -/
theorem twoCopyPort_Aedge_fanout_of_ambientGirth
    [Fintype I] [Nonempty I]
    {Y : I → HypergraphPiece W}
    (hForest : ForestOfCopies Y)
    (p : I) (S : Set W)
    (hS : S ∈ (Y p).edges)
    (H : Set (Set W)) (g : ℕ)
    (hg : 2 ≤ g)
    (hOwnerSupport : (Y p).edges ⊆ H)
    (hGirth : GirthGT H g) :
    ForestOfCopies
      (sumPieces
        (fun i : I => (Y i).map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} =>
          (Y p).map (twoCopyPortRight S))) ∧
    GirthGT
      (injectedEdgeFamily (twoCopyPortLeft S) H ∪
        injectedEdgeFamily (twoCopyPortRight S) (Y p).edges) g := by
  have hTwo : GirthGT H 2 := girthGT_mono hGirth hg
  have hOwnerLinear : LinearEdgeSet (Y p).edges :=
    ownerLinear_of_ambientGirthTwo H (Y p) hOwnerSupport hTwo
  exact twoCopyPort_Aedge_fanout_invariants
    hForest p S hS hOwnerLinear H g hOwnerSupport hGirth

end StructuralRamsey.Girth
