import Girth.ForestJoinLift

/-! # Forests with disjoint outer components

Disjoint components are the base case of the manuscript's initial picture.
Any nonempty finite family of pairwise disjoint outer pieces admits a join tree:
take an arbitrary star.  If each outer piece carries a local forest, the
generic join-tree lifting theorem combines them with no separator bookkeeping.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- Pairwise disjoint carriers are pairwise allowed intersections. -/
theorem pairwiseAllowed_of_disjoint
    {P : Q → HypergraphPiece W}
    (hDisj :
      ∀ ⦃q r : Q⦄, q ≠ r →
        Disjoint (P q).carrier (P r).carrier) :
    PairwiseAllowed P := by
  intro q r hqr
  left
  intro x hx y hy
  exfalso
  exact Set.disjoint_left.mp (hDisj hqr) hx.1 hx.2

/-- A nonempty finite pairwise-disjoint family has a join tree.  The star
center may be chosen arbitrarily because every occurrence set is subsingleton. -/
noncomputable def joinTree_of_disjoint
    [Fintype Q] [Nonempty Q]
    {P : Q → HypergraphPiece W}
    (hDisj :
      ∀ ⦃q r : Q⦄, q ≠ r →
        Disjoint (P q).carrier (P r).carrier) :
    JoinTree P := by
  classical
  let q0 : Q := Classical.choice (inferInstance : Nonempty Q)
  refine
    { tree := SimpleGraph.starGraph q0
      isTree := SimpleGraph.isTree_starGraph q0
      running := ?_ }
  intro x
  have hOcc :
      ({q : Q | x ∈ (P q).carrier}).Subsingleton := by
    intro q hq r hr
    by_contra hne
    exact Set.disjoint_left.mp (hDisj hne) hq hr
  letI : Subsingleton {q : Q | x ∈ (P q).carrier} :=
    hOcc.coe_sort
  exact SimpleGraph.Preconnected.of_subsingleton

/-- Hence a nonempty finite pairwise-disjoint family is a forest. -/
theorem forestOfCopies_of_disjoint
    [Fintype Q] [Nonempty Q]
    {P : Q → HypergraphPiece W}
    (hDisj :
      ∀ ⦃q r : Q⦄, q ≠ r →
        Disjoint (P q).carrier (P r).carrier) :
    ForestOfCopies P :=
  ⟨pairwiseAllowed_of_disjoint hDisj,
    Or.inr ⟨joinTree_of_disjoint hDisj⟩⟩

/-- Combine nonempty local forests sitting in pairwise-disjoint outer pieces. -/
theorem forestOfCopies_lift_disjoint
    {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hDisj :
      ∀ ⦃q r : Q⦄, q ≠ r →
        Disjoint (P q).carrier (P r).carrier)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, ForestOfCopies (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier) :
    ForestOfCopies (fun z : Sigma K => F z.1 z.2) := by
  classical
  let JOuter : JoinTree P :=
    joinTree_of_disjoint hDisj
  let connector : (q r : Q) → K q :=
    fun q _ => Classical.choice (inferInstance : Nonempty (K q))
  have hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier := by
    intro q r hadj x hx
    have hqr : q ≠ r := hadj.ne
    exact (Set.disjoint_left.mp (hDisj hqr) hx.1 hx.2).elim
  have hCross :
      ∀ ⦃q r : Q⦄, q ≠ r →
        ∀ (i : K q) (j : K r),
          AllowedIntersection (F q i) (F r j) := by
    intro q r hqr i j
    left
    intro x hx y hy
    exfalso
    exact
      Set.disjoint_left.mp (hDisj hqr)
        (hContain q i hx.1) (hContain r j hx.2)
  exact
    forestOfCopies_lift_local
      (pairwiseAllowed_of_disjoint hDisj)
      JOuter
      (fun q => (hLocal q).pairwiseAllowed)
      (fun q =>
        Classical.choice
          ((hLocal q).joinTree_of_nonempty))
      hContain
      connector
      hConnector
      hCross

end StructuralRamsey.Girth
