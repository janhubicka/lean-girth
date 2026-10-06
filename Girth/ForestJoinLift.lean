import Girth.ForestJoinGlue
import Girth.ForestReindex
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Sum

/-! # Lifting a join tree of local forests

This packages the combinatorial core of Lemma "Lifting a join tree" from the
manuscript. An outer join tree indexes local join trees. Local members stay
inside their owner pieces, and every outer separator is carried by a designated
connector member on each side. Peeling an outer leaf and applying the binary
join-tree glue therefore yields a join tree on the total dependent family.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- Split a dependent family at one distinguished outer index. -/
noncomputable def sigmaSplitAt
    (K : Q → Type v) (leaf : Q) :
    (Sigma (fun q : {q : Q // q ≠ leaf} => K q.1) ⊕ K leaf) ≃
      Sigma K := by
  classical
  refine
    { toFun := fun s =>
        match s with
        | .inl z => ⟨z.1.1, z.2⟩
        | .inr k => ⟨leaf, k⟩
      invFun := fun z =>
        if h : z.1 = leaf then
          Sum.inr (h ▸ z.2)
        else
          Sum.inl ⟨⟨z.1, h⟩, z.2⟩
      left_inv := by
        intro s
        cases s with
        | inl z =>
            simp [z.1.2]
        | inr k =>
            simp
      right_inv := by
        intro z
        rcases z with ⟨q, k⟩
        by_cases h : q = leaf
        · subst q
          simp
        · simp [h] }

/-- A join tree on one local fiber induces a join tree on the total dependent
family when the outer index type is subsingleton. -/
theorem joinTree_sigma_of_subsingleton
    {Q : Type v} {K : Q → Type v}
    [Nonempty Q] [Subsingleton Q]
    {F : (q : Q) → K q → HypergraphPiece W}
    (J : ∀ q : Q, JoinTree (F q)) :
    Nonempty
      (JoinTree (fun z : Sigma K => F z.1 z.2)) := by
  classical
  let q0 : Q := Classical.choice (inferInstance : Nonempty Q)
  let e : Sigma K ≃ K q0 :=
    { toFun := fun z =>
        (Subsingleton.elim z.1 q0) ▸ z.2
      invFun := fun k => ⟨q0, k⟩
      left_inv := by
        intro z
        rcases z with ⟨q, k⟩
        have h : q = q0 := Subsingleton.elim _ _
        subst q
        rfl
      right_inv := by
        intro k
        rfl }
  have hFam :
      (fun z : Sigma K => F q0 (e z)) =
        (fun z : Sigma K => F z.1 z.2) := by
    funext z
    rcases z with ⟨q, k⟩
    have hq : q = q0 := Subsingleton.elim _ _
    subst q
    simp [e]
  rw [← hFam]
  exact ⟨(J q0).reindex e⟩

/-- Outer-tree lifting of local join trees.

P q is the outer piece at owner q, F q k are the local members assigned to
that owner, and connector q r is the local member on side q chosen to carry
the separator toward r. -/
theorem joinTree_lift_local
    {Q : Type v} {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (JOuter : JoinTree P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (JLocal : ∀ q : Q, JoinTree (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (connector : (q r : Q) → K q)
    (hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier)
    (hCrossAllowed :
      ∀ ⦃q r : Q⦄, q ≠ r →
        ∀ (i : K q) (j : K r),
          AllowedIntersection (F q i) (F r j)) :
    Nonempty
      (JoinTree (fun z : Sigma K => F z.1 z.2)) := by
  classical
  by_cases hsub : Subsingleton Q
  · letI : Subsingleton Q := hsub
    exact joinTree_sigma_of_subsingleton JLocal
  · letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨leaf, parent, hadj, huniq, _hLeafInter⟩ :=
      JOuter.exists_leaf_attachment
    let p : {q : Q // q ≠ leaf} :=
      ⟨parent, hadj.ne.symm⟩
    let reindexRest :
        {q : Q // q ≠ leaf} ≃
          {q : Q // q ∈ (({leaf} : Set Q)ᶜ)} :=
      Equiv.subtypeEquivRight (fun q => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff])
    let JRest :
        JoinTree (fun q : {q : Q // q ≠ leaf} => P q.1) := by
      simpa [erasePiece, reindexRest] using
        (JOuter.eraseLeaf hadj huniq).reindex reindexRest
    let KRest : {q : Q // q ≠ leaf} → Type v :=
      fun q => K q.1
    let FRest :
        (q : {q : Q // q ≠ leaf}) →
          KRest q → HypergraphPiece W :=
      fun q k => F q.1 k
    let connectorRest :
        (q r : {q : Q // q ≠ leaf}) → KRest q :=
      fun q r => connector q.1 r.1
    have hContainRest :
        ∀ q (k : KRest q),
          (FRest q k).carrier ⊆ (P q.1).carrier := by
      intro q k
      exact hContain q.1 k
    have hConnectorRest :
        ∀ ⦃q r : {q : Q // q ≠ leaf}⦄,
          JRest.tree.Adj q r →
            (P q.1).carrier ∩ (P r.1).carrier ⊆
              (FRest q (connectorRest q r)).carrier := by
      intro q r hqr
      have hqr0 :
          (JOuter.eraseLeaf hadj huniq).tree.Adj
            (reindexRest q) (reindexRest r) := by
        exact hqr
      have hqr1 :
          JOuter.tree.Adj (reindexRest q).1 (reindexRest r).1 := by
        exact hqr0
      have hqr' : JOuter.tree.Adj q.1 r.1 := by
        simpa [reindexRest] using hqr1
      exact hConnector hqr'
    have hCrossRest :
        ∀ ⦃q r : {q : Q // q ≠ leaf}⦄, q ≠ r →
          ∀ (i : KRest q) (j : KRest r),
            AllowedIntersection (FRest q i) (FRest r j) := by
      intro q r hqr i j
      apply hCrossAllowed
      intro hval
      apply hqr
      exact Subtype.ext hval
    letI : Nonempty {q : Q // q ≠ leaf} := ⟨p⟩
    have hcard :
        Fintype.card {q : Q // q ≠ leaf} < Fintype.card Q := by
      apply Fintype.card_lt_of_injective_not_surjective
        (fun q : {q : Q // q ≠ leaf} => q.1)
        Subtype.val_injective
      intro hsurj
      obtain ⟨q, hq⟩ := hsurj leaf
      exact q.2 hq
    obtain ⟨JTotRest⟩ :=
      joinTree_lift_local
        (Q := {q : Q // q ≠ leaf})
        (K := KRest)
        (P := fun q => P q.1)
        JRest
        (fun q => JLocal q.1)
        hContainRest
        connectorRest
        hConnectorRest
        hCrossRest
    let TotRest := Sigma KRest
    let familyRest : TotRest → HypergraphPiece W :=
      fun z => FRest z.1 z.2
    let restConnector : TotRest :=
      ⟨p, connector parent leaf⟩
    let leafConnector : K leaf :=
      connector leaf parent
    have hCrossOcc :
        ∀ (x : W) (z : TotRest) (k : K leaf),
          x ∈ (familyRest z).carrier →
          x ∈ (F leaf k).carrier →
            x ∈ (familyRest restConnector).carrier ∧
              x ∈ (F leaf leafConnector).carrier := by
      intro x z k hxRest hxLeaf
      have hxOtherP : x ∈ (P z.1.1).carrier :=
        hContain z.1.1 z.2 hxRest
      have hxLeafP : x ∈ (P leaf).carrier :=
        hContain leaf k hxLeaf
      have hxParentP : x ∈ (P parent).carrier :=
        JOuter.mem_parent_of_mem_leaf_and_other
          hadj huniq z.1.2 hxLeafP hxOtherP
      have hxParentConn :
          x ∈ (F parent (connector parent leaf)).carrier :=
        hConnector hadj.symm ⟨hxParentP, hxLeafP⟩
      have hxLeafConn :
          x ∈ (F leaf (connector leaf parent)).carrier :=
        hConnector hadj ⟨hxLeafP, hxParentP⟩
      exact ⟨hxParentConn, hxLeafConn⟩
    have hCrossAllowedLeaf :
        ∀ (z : TotRest) (k : K leaf),
          AllowedIntersection (familyRest z) (F leaf k) := by
      intro z k
      exact
        hCrossAllowed z.1.2 z.2 k
    let JSum :
        JoinTree (sumPieces familyRest (F leaf)) :=
      JTotRest.sumBridge
        (JLocal leaf)
        restConnector leafConnector hCrossOcc
    let e :
        (TotRest ⊕ K leaf) ≃ Sigma K :=
      sigmaSplitAt K leaf
    have hFam :
        (fun z : Sigma K =>
          sumPieces familyRest (F leaf) (e.symm z)) =
        (fun z : Sigma K => F z.1 z.2) := by
      funext z
      rcases z with ⟨q, k⟩
      by_cases hq : q = leaf
      · subst q
        simp [e, sigmaSplitAt, sumPieces]
      · simp [e, sigmaSplitAt, sumPieces, hq,
          TotRest, familyRest, FRest, KRest]
    rw [← hFam]
    exact ⟨JSum.reindex e.symm⟩
termination_by Fintype.card Q
decreasing_by
  exact hcard

/-- Forest wrapper for the outer-tree lifting theorem. -/
theorem forestOfCopies_lift_local
    {Q : Type v} {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuterAllowed : PairwiseAllowed P)
    (JOuter : JoinTree P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocalAllowed : ∀ q : Q, PairwiseAllowed (F q))
    (JLocal : ∀ q : Q, JoinTree (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (connector : (q r : Q) → K q)
    (hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier)
    (hCrossAllowed :
      ∀ ⦃q r : Q⦄, q ≠ r →
        ∀ (i : K q) (j : K r),
          AllowedIntersection (F q i) (F r j)) :
    ForestOfCopies (fun z : Sigma K => F z.1 z.2) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    rcases a with ⟨q, i⟩
    rcases b with ⟨r, j⟩
    by_cases hqr : q = r
    · subst r
      apply hLocalAllowed q
      intro hij
      apply hab
      cases hij
      rfl
    · exact hCrossAllowed hqr i j
  · exact Or.inr
      (joinTree_lift_local
        JOuter JLocal hContain connector hConnector hCrossAllowed)

end StructuralRamsey.Girth
