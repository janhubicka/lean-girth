import Girth.ForestCompletionKeep

/-! # Canonical retention by equality of support pieces

Local completion witnesses need not reuse the selected *labels*.  They only
promise that each selected support piece occurs among the completed pieces.
The correct keep-set therefore retains every completed label whose piece
equals a selected piece, as well as every designated completed piece.
The remaining labels are precisely removable one-edge auxiliaries.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Variant of the local assembly theorem that classifies members by equality
of support pieces rather than equality of their labels.  This is the form
provided by the finite quantified completion property. -/
theorem forestCompletion_witness_of_local_piece_classification
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
        (∃ n : N,
          F z.1 z.2 = F (selected n).1 (selected n).2) ∨
        designated (F z.1 z.2) ∨
        (F z.1 z.2).IsOneEdge) :
    ∃ keep : Finset (Sigma K),
      ForestCompletionWitness
        (fun n : N => F (selected n).1 (selected n).2)
        designated
        (fun z : {z : Sigma K // z ∈ keep} => F z.1.1 z.1.2) := by
  classical
  let keep : Finset (Sigma K) :=
    Finset.univ.filter (fun z : Sigma K =>
      (∃ n : N, F z.1 z.2 = F (selected n).1 (selected n).2) ∨
      designated (F z.1 z.2))
  have hKeep : ∀ n : N, selected n ∈ keep := by
    intro n
    have h : (∃ j : N,
        F (selected n).1 (selected n).2 =
          F (selected j).1 (selected j).2) ∨
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
  obtain ⟨_hBudget, hForest, hSelected⟩ :=
    forestCompletion_assemble_of_ambient_girth
      hOuter JOuter hEdges hGirth
      hLocalAllowed JLocal hContain
      connector hConnector hConnectorEdge
      owner hSurj m hCard selected
      hSelectedOwner keep hKeep hAux
  refine ⟨keep, hForest, ?_, ?_⟩
  · intro n
    obtain ⟨z, hz, _⟩ := hSelected n
    exact ⟨z, congrArg (fun s : Sigma K => F s.1 s.2) hz⟩
  · intro z
    exact (Finset.mem_filter.mp z.property).2

end StructuralRamsey.Girth
