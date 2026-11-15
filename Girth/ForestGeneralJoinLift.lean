import Girth.ForestBinarySeparatorLift
import Girth.ForestJoinLift
import Girth.ForestAuxiliaryDeletion

/-!
# General join-tree lifting without support requests at singleton separators

This is a *source-level candidate* for the general strengthening of
the manuscript's join-tree lifting lemma. It requires genuine
one-edge connector members only when the corresponding outer
separator is NOT subsingleton. At empty and singleton separators
the two completed forests are joined directly, even if neither
contains the shared vertex.

The proof follows the existing forest join-lift recursion on
the number of outer owners, but replaces unconditional
support-covering connector choices by the binary small/whole-edge
gluing lemmas in ForestBinarySeparatorLift.

No local Lean compiler was available during development, so
the exact-head build and #print axioms still must run.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- Lift nonempty local forests over an outer join tree when only
NON-SINGLETON outer separators carry an explicitly retained
one-edge request on each side. There is no support-edge-coverage
assumption at singleton or empty separators.

The output retains every local member, including requests; the
finite short-auxiliary deletion operation can be applied separately
to remove precisely unselected separator requests. -/
theorem forestOfCopies_lift_local_without_singleton_requests
    {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q : Q, Fintype (K q)]
    [∀ q : Q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (JOuter : JoinTree P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, ForestOfCopies (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (hEdgeRequest :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
        ∃ k : K q,
          F q k = HypergraphPiece.oneEdge
            ((P q).carrier ∩ (P r).carrier)) :
    ForestOfCopies (fun z : Sigma K => F z.1 z.2) := by
  classical
  by_cases hSub : Subsingleton Q
  · letI : Subsingleton Q := hSub
    have hTotalAllowed :
        PairwiseAllowed (fun z : Sigma K => F z.1 z.2) := by
      intro a b hab
      rcases a with ⟨q, i⟩
      rcases b with ⟨r, j⟩
      have hqr : r = q := Subsingleton.elim r q
      subst r
      apply (hLocal q).pairwiseAllowed
      intro hij
      apply hab
      cases hij
      rfl
    have hTotalTree :
        Nonempty (JoinTree (fun z : Sigma K => F z.1 z.2)) :=
      joinTree_sigma_of_subsingleton
        (fun q : Q =>
          Classical.choice ((hLocal q).joinTree_of_nonempty))
    exact ⟨hTotalAllowed, Or.inr hTotalTree⟩
  · letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hSub
    obtain ⟨leaf, parent, hadj, huniq, _hLeafInter⟩ :=
      JOuter.exists_leaf_attachment
    let R := {q : Q // q ≠ leaf}
    let p : R := ⟨parent, hadj.ne.symm⟩
    letI : Nonempty R := ⟨p⟩
    let reindexRest :
        R ≃ {q : Q // q ∈ (({leaf} : Set Q)ᶜ)} :=
      Equiv.subtypeEquivRight (fun q => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
    let JRest : JoinTree (fun q : R => P q.1) := by
      simpa [erasePiece, reindexRest] using
        (JOuter.eraseLeaf hadj huniq).reindex reindexRest
    let KRest : R → Type v := fun q => K q.1
    let FRest :
        (q : R) → KRest q → HypergraphPiece W :=
      fun q k => F q.1 k
    have hLocalRest : ∀ q : R, ForestOfCopies (FRest q) :=
      fun q => hLocal q.1
    have hContainRest :
        ∀ q : R, ∀ k : KRest q,
          (FRest q k).carrier ⊆ (P q.1).carrier := by
      intro q k
      exact hContain q.1 k
    have hRequestRest :
        ∀ ⦃q r : R⦄ (hqr : JRest.tree.Adj q r),
          ¬((P q.1).carrier ∩ (P r.1).carrier).Subsingleton →
          ∃ k : KRest q,
            FRest q k = HypergraphPiece.oneEdge
              ((P q.1).carrier ∩ (P r.1).carrier) := by
      intro q r hqr hBig
      have hqr0 :
          (JOuter.eraseLeaf hadj huniq).tree.Adj
            (reindexRest q) (reindexRest r) := by
        exact hqr
      have hqr1 : JOuter.tree.Adj
          (reindexRest q).1 (reindexRest r).1 := by
        exact hqr0
      have hqr' : JOuter.tree.Adj q.1 r.1 := by
        simpa [reindexRest] using hqr1
      exact hEdgeRequest hqr' hBig
    have hcard :
        Fintype.card R < Fintype.card Q := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun q : R => q.1) Subtype.val_injective
      intro hSurj
      obtain ⟨q, hq⟩ := hSurj leaf
      exact q.2 hq
    have hRest :
        ForestOfCopies
          (fun z : Sigma KRest => FRest z.1 z.2) :=
      forestOfCopies_lift_local_without_singleton_requests
        (Q := R) (K := KRest)
        (P := fun q => P q.1) (F := FRest)
        JRest hLocalRest hContainRest hRequestRest
    let familyRest : Sigma KRest → HypergraphPiece W :=
      fun z => FRest z.1 z.2
    let S : Set W :=
      (P leaf).carrier ∩ (P parent).carrier
    have hCross :
        ∀ (z : Sigma KRest) (k : K leaf),
          (familyRest z).carrier ∩ (F leaf k).carrier ⊆ S := by
      intro z k x hx
      have hxOther : x ∈ (P z.1.1).carrier :=
        hContain z.1.1 z.2 hx.1
      have hxLeaf : x ∈ (P leaf).carrier :=
        hContain leaf k hx.2
      have hxParent : x ∈ (P parent).carrier :=
        JOuter.mem_parent_of_mem_leaf_and_other
          hadj huniq z.1.2 hxLeaf hxOther
      exact ⟨hxLeaf, hxParent⟩
    have hJoined :
        ForestOfCopies (sumPieces familyRest (F leaf)) := by
      by_cases hSmall : S.Subsingleton
      · apply forestOfCopies_sum_of_subsingleton_overlap
          hRest (hLocal leaf)
        intro x hx y hy
        obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx.1
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx.2
        obtain ⟨z', hz'⟩ := Set.mem_iUnion.mp hy.1
        obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp hy.2
        exact hSmall (hCross z k ⟨hz, hk⟩)
          (hCross z' k' ⟨hz', hk'⟩)
      · have hSmallRev :
            ¬((P parent).carrier ∩ (P leaf).carrier).Subsingleton := by
          simpa [S, Set.inter_comm] using hSmall
        obtain ⟨kLeaf, hkLeaf⟩ := hEdgeRequest hadj hSmall
        obtain ⟨kParent, hkParent⟩ :=
          hEdgeRequest hadj.symm hSmallRev
        let i0 : Sigma KRest := ⟨p, kParent⟩
        have hReqRest :
            familyRest i0 = HypergraphPiece.oneEdge S := by
          simpa [familyRest, FRest, i0, p, S,
            Set.inter_comm] using hkParent
        have hReqLeaf :
            F leaf kLeaf = HypergraphPiece.oneEdge S := by
          simpa [S] using hkLeaf
        exact forestOfCopies_sum_of_common_edge
          hRest (hLocal leaf) S i0 kLeaf
          hReqRest hReqLeaf hCross
    let familyTotal : Sigma K → HypergraphPiece W :=
      fun z => F z.1 z.2
    let split : (Sigma KRest ⊕ K leaf) ≃ Sigma K :=
      sigmaSplitAt K leaf
    have hFam :
        (fun z : Sigma K =>
          sumPieces familyRest (F leaf) (split.symm z)) =
        familyTotal := by
      funext z
      rcases z with ⟨q, k⟩
      by_cases hq : q = leaf
      · subst q
        simp [split, sigmaSplitAt, sumPieces,
          familyTotal]
      · simp [split, sigmaSplitAt, sumPieces, hq,
          familyTotal, familyRest, FRest, KRest]
    have hResult : ForestOfCopies familyTotal := by
      rw [← hFam]
      exact hJoined.reindex split.symm
    exact hResult
termination_by Fintype.card Q
decreasing_by
  exact hcard


/-- General lifting followed by deletion of exactly the unselected
one-edge requests. The keep set may include local designated
completion additions or requested edge members which coincide with
selected members; only its COMPLEMENT has to be auxiliary.

This is the labelled form needed before converting back to the
manuscript's finite SET of actual selected and added members. -/
theorem forestOfCopies_lift_without_singleton_then_delete
    {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q : Q, Fintype (K q)]
    [∀ q : Q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (JOuter : JoinTree P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, ForestOfCopies (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (hEdgeRequest :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
        ∃ k : K q,
          F q k = HypergraphPiece.oneEdge
            ((P q).carrier ∩ (P r).carrier))
    (keep : Finset (Sigma K))
    (hAuxiliary :
      ∀ z : Sigma K, z ∉ keep → (F z.1 z.2).IsOneEdge) :
    ForestOfCopies
      (fun z : {z : Sigma K // z ∈ keep} => F z.1.1 z.1.2) := by
  classical
  have hWhole :
      ForestOfCopies (fun z : Sigma K => F z.1 z.2) :=
    forestOfCopies_lift_local_without_singleton_requests
      JOuter hLocal hContain hEdgeRequest
  exact hWhole.restrict_of_oneEdge_outside keep hAuxiliary

end StructuralRamsey.Girth
