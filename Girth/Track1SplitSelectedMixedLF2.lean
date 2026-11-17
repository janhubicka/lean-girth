import Girth.Track1FullSelectedSupportPieces
import Girth.ForestMixedOneEdgeOwners
import Girth.TrainRecursiveBaseRamsey
import Girth.LinearityGirthTwo
import Mathlib.Tactic

/-!
# Track 1: the selected SPLIT witness itself has complete mixed LF2

This is the actual predecessor forest bound for a nontrivial
cutoff-three picture step. Work with selected lifted B-support pieces
and EVERY ambient positive split edge, including those not in any
particular designated B-copy.

The only inputs are:
* selected B-pieces have pairwise allowed intersections;
* each selected piece is A-edge-strong in the physical split support;
* the split physical ambient support is linear.

Any pair of such members has an allowed intersection. Since a family
with at most two members and pairwise allowed intersections is a
forest, the entire labelled mixed family has LocalForestThrough 2.

This avoids transferring LF2 through an extra unsplit EHN relational
model. It uses the same two-member star argument as the existing
checked TrainRecursiveBaseRamsey base case.

STAGED DRAFT; the following code has not been kernel-checked.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I Choice W : Type v}

/-- Any family of at most two pieces is a forest as soon as
each pair of distinct members has an allowed intersection.
This is the general combinatorial two-member observation used
in the checked local Ramsey base case. -/
theorem track1_forestOfCopies_two_of_pairwise
    {J : Type v} [Fintype J]
    (F : J → HypergraphPiece W)
    (hCard : Fintype.card J ≤ 2)
    (hPair : PairwiseAllowed F) :
    ForestOfCopies F := by
  classical
  by_cases hN : Nonempty J
  · obtain ⟨root⟩ := hN
    let K := {j : J // j ≠ root}
    have hKCard : Fintype.card K ≤ 1 := by
      have hEq := Fintype.card_congr (Equiv.optionSubtypeNe root)
      simp only [Fintype.card_option] at hEq
      change Fintype.card K + 1 = Fintype.card J at hEq
      omega
    letI : Subsingleton K := Fintype.card_le_one_iff_subsingleton.mp hKCard
    refine ⟨hPair, Or.inr ⟨{
      tree := SimpleGraph.starGraph root
      isTree := SimpleGraph.isTree_starGraph root
      running := ?_ }⟩⟩
    intro x
    by_cases hx : x ∈ (F root).carrier
    · exact starGraph_induce_preconnected_of_mem_center root hx
    · have hNonroot : ∀ j : {j : J | x ∈ (F j).carrier}, j.1 ≠ root := by
        intro j hEq
        have hj : x ∈ (F j.1).carrier := j.2
        exact hx (by simpa only [hEq] using hj)
      letI : Subsingleton {j : J | x ∈ (F j).carrier} := ⟨by
        intro a b
        apply Subtype.ext
        exact congrArg (fun k : K => k.1)
          (Subsingleton.elim
            (⟨a.1, hNonroot a⟩ : K)
            (⟨b.1, hNonroot b⟩ : K))⟩
      exact SimpleGraph.Preconnected.of_subsingleton
  · letI : IsEmpty J := ⟨fun j => hN ⟨j⟩⟩
    exact ⟨hPair, Or.inl inferInstance⟩

/-- Extend pairwise allowedness to the honest indexed subfamilies of
at most two selected members. No unique-owner assumption is needed. -/
theorem track1_localForestThrough_two_of_pairwise
    (F : Choice → HypergraphPiece W)
    (hPair : PairwiseAllowed F) :
    LocalForestThrough F 2 := by
  classical
  intro J _ idx hCard
  apply track1_forestOfCopies_two_of_pairwise
    (fun j : J => F (idx j)) hCard
  intro i j hij
  exact hPair (fun h => hij (idx.injective h))

/-- A genuine selected B-support piece meets an ambient physical edge
in a singleton or the full edge, provided every split edge meeting
the selected B-carrier twice belongs to that B-copy. -/
theorem track1_selectedLift_vs_splitEdge_allowed
    (H : ColouredEdgeOwnerSplit V I)
    (S : ColouredOwnerSelectedCopy (W := W) H)
    (hStrong : ∀ f : H.OldEdge, ∀ z w : H.Vertex,
      z ≠ w → z ∈ H.splitEdge f → w ∈ H.splitEdge f →
      z ∈ Set.range S.lift → w ∈ Set.range S.lift →
      ∃ a : S.SourceEdge, S.physicalEdge a = f)
    (f : H.OldEdge) :
    AllowedIntersection S.selectedLiftSupportPiece
      (HypergraphPiece.oneEdge (H.splitEdge f)) := by
  classical
  change (Set.range S.lift ∩ H.splitEdge f).Subsingleton ∨
    ∃ e : Set H.Vertex,
      e ∈ S.selectedLiftSupportPiece.edges ∧
      e ∈ (HypergraphPiece.oneEdge (H.splitEdge f)).edges ∧
      Set.range S.lift ∩ H.splitEdge f = e
  by_cases hSmall : (Set.range S.lift ∩ H.splitEdge f).Subsingleton
  · exact Or.inl hSmall
  · have hPair : ∃ z w : H.Vertex,
        z ∈ Set.range S.lift ∩ H.splitEdge f ∧
        w ∈ Set.range S.lift ∩ H.splitEdge f ∧ z ≠ w := by
      by_contra hNo
      apply hSmall
      intro z hz w hw
      by_contra hne
      exact hNo ⟨z, w, hz, hw, hne⟩
    obtain ⟨z, w, hz, hw, hzw⟩ := hPair
    obtain ⟨a, ha⟩ :=
      hStrong f z w hzw hz.2 hw.2 hz.1 hw.1
    have hFull : H.splitEdge f ⊆ Set.range S.lift := by
      rw [← ha]
      exact S.split_selected_edge_subset_copy a
    have hBEdge : H.splitEdge f ∈ S.selectedLiftSupportPiece.edges := by
      exact ⟨a, (congrArg H.splitEdge ha).symm⟩
    refine Or.inr ⟨H.splitEdge f, hBEdge, ?_, ?_⟩
    · simp [HypergraphPiece.oneEdge]
    · exact Set.inter_eq_right.mpr hFull

/-- Every pair in the complete mixed family (actual lifted selected B
pieces plus ALL ambient split one-edge members) is allowed. -/
theorem track1_selectedSplitMixed_pairwiseAllowed
    (H : ColouredEdgeOwnerSplit V I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hBPair : PairwiseAllowed
      (fun c : Choice => (selected c).selectedLiftSupportPiece))
    (hStrong : ∀ c : Choice, ∀ f : H.OldEdge, ∀ z w : H.Vertex,
      z ≠ w → z ∈ H.splitEdge f → w ∈ H.splitEdge f →
      z ∈ Set.range (selected c).lift →
      w ∈ Set.range (selected c).lift →
      ∃ a : (selected c).SourceEdge, (selected c).physicalEdge a = f)
    (hLinear : GirthGT H.splitPhysicalEdges 2) :
    PairwiseAllowed
      (mixedOwnerSmall
        (fun c : Choice => (selected c).selectedLiftSupportPiece)
        (fun f : H.OldEdge => H.splitEdge f)) := by
  intro x y hxy
  cases x with
  | inl c =>
      cases y with
      | inl d =>
          exact hBPair (by intro h; exact hxy (congrArg Sum.inl h))
      | inr f =>
          exact track1_selectedLift_vs_splitEdge_allowed
            H (selected c) (hStrong c) f
  | inr f =>
      cases y with
      | inl c =>
          exact allowedIntersection_symm
            (track1_selectedLift_vs_splitEdge_allowed
              H (selected c) (hStrong c) f)
      | inr g =>
          left
          change (H.splitEdge f ∩ H.splitEdge g).Subsingleton
          have hfg : f ≠ g := by
            intro h
            exact hxy (congrArg Sum.inr h)
          exact (pairwise_subsingleton_of_girthGT_two hLinear)
            (show H.splitEdge f ∈ H.splitPhysicalEdges from ⟨f, rfl⟩)
            (show H.splitEdge g ∈ H.splitPhysicalEdges from ⟨g, rfl⟩)
            (fun h => hfg (H.splitEdge_injective h))

/-- The complete split selected-witness family automatically has
the mixed predecessor LF2 property needed for the cutoff-three
picture step, with NO unproved local-forest input. -/
theorem track1_actualSplitSelected_mixedLF2
    (H : ColouredEdgeOwnerSplit V I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hBPair : PairwiseAllowed
      (fun c : Choice => (selected c).selectedLiftSupportPiece))
    (hStrong : ∀ c : Choice, ∀ f : H.OldEdge, ∀ z w : H.Vertex,
      z ≠ w → z ∈ H.splitEdge f → w ∈ H.splitEdge f →
      z ∈ Set.range (selected c).lift →
      w ∈ Set.range (selected c).lift →
      ∃ a : (selected c).SourceEdge, (selected c).physicalEdge a = f)
    (hLinear : GirthGT H.splitPhysicalEdges 2) :
    LocalForestThrough
      (mixedOwnerSmall
        (fun c : Choice => (selected c).selectedLiftSupportPiece)
        (fun f : H.OldEdge => H.splitEdge f)) 2 := by
  exact track1_localForestThrough_two_of_pairwise
    _ (track1_selectedSplitMixed_pairwiseAllowed
      H selected hBPair hStrong hLinear)

#print axioms StructuralRamsey.Girth.track1_forestOfCopies_two_of_pairwise
#print axioms StructuralRamsey.Girth.track1_localForestThrough_two_of_pairwise
#print axioms StructuralRamsey.Girth.track1_selectedLift_vs_splitEdge_allowed
#print axioms StructuralRamsey.Girth.track1_selectedSplitMixed_pairwiseAllowed
#print axioms StructuralRamsey.Girth.track1_actualSplitSelected_mixedLF2

end StructuralRamsey.Girth
