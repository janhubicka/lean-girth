import Girth.ForestCompletionWitness

/-! # Canonical retention of selected and designated pieces

The local completion step may introduce auxiliary one-edge connectors.
Rather than carrying an arbitrary keep-set and later proving its properties,
retain exactly the selected labels and the designated pieces.  Every other
label is a one-edge auxiliary and can be deleted without breaking the forest.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- A local assembled completion needs no separately chosen keep-set once
every member is selected, designated, or a one-edge auxiliary.  The chosen
keep-set is precisely the selected and designated labels. -/
theorem forestCompletion_witness_of_local_classification
    [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype N]
    {K : Q → Type v}
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
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
    (hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selected : N → Sigma K)
    (hSelectedOwner : ∀ n : N, (selected n).1 = owner n)
    (designated : HypergraphPiece W → Prop)
    (hClassification :
      ∀ z : Sigma K,
        (∃ n : N, z = selected n) ∨
        designated (F z.1 z.2) ∨
        (F z.1 z.2).IsOneEdge) :
    ∃ keep : Finset (Sigma K),
      ForestCompletionWitness
        (fun n : N => F (selected n).1 (selected n).2)
        designated
        (fun z : {z : Sigma K // z ∈ keep} => F z.1.1 z.1.2) := by
  classical
  let keep : Finset (Sigma K) :=
    Finset.univ.filter
      (fun z => (∃ n : N, z = selected n) ∨
        designated (F z.1 z.2))
  have hKeep : ∀ n : N, selected n ∈ keep := by
    intro n
    have h : (∃ j : N, selected n = selected j) ∨
        designated (F (selected n).1 (selected n).2) :=
      Or.inl ⟨n, rfl⟩
    simpa [keep] using h
  have hAux : ∀ z : Sigma K, z ∉ keep →
      (F z.1 z.2).IsOneEdge := by
    intro z hz
    rcases hClassification z with hSel | hDes | hOne
    · exfalso
      apply hz
      simp [keep, hSel]
    · exfalso
      apply hz
      simp [keep, hDes]
    · exact hOne
  have hClassify : ∀ z : Sigma K, z ∈ keep →
      (∃ n : N, z = selected n) ∨
        designated (F z.1 z.2) := by
    intro z hz
    simpa [keep] using hz
  refine ⟨keep, ?_⟩
  exact forestCompletion_witness_of_local_assembly
    hOuter JOuter hEdges hGirth
    hLocalAllowed JLocal hContain
    connector hConnector hConnectorEdge
    owner hSurj m hCard selected hSelectedOwner
    keep hKeep hAux designated hClassify

end StructuralRamsey.Girth
