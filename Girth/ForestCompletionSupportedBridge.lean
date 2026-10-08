import Girth.ForestCompletionSeparatorRequests

/-! # Global forest completion with automatically chosen separator requests

The general completion-assembly theorem asks for a tested request at every
outer join-tree neighbour, together with a proof that it covers the separator
and equals the separator in the non-subsingleton case. These requests need
not be independent choices: if the outer pieces have nonempty, vertex-covering
support edge families and ambient support girth is greater than two, the
geometric separator lemma constructs them as actual one-edge pieces.

Consequently, only the classification of selected and one-edge requests
as tested local members, and the transport of designated members, remain
external to the combinatorial completion argument.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- A quantified completion property in each standard picture yields a
designated global completion. The one-edge connector requests and their
exact intersection identities are *constructed*, not separately assumed. -/
theorem ForestCompletionProperty.assemble_over_joinTree_of_supported_separators
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    [DecidableRel JOuter.tree.Adj]
    {H : Set (Set W)}
    (hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄, e ∈ (P q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
    (hNonempty : ∀ q, (P q).edges.Nonempty)
    (hVertexCover :
      ∀ q (x : W), x ∈ (P q).carrier →
        ∃ e : Set W, e ∈ (P q).edges ∧ x ∈ e)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (hSelectedContained :
      ∀ n : N,
        (selectedGlobal n).carrier ⊆ (P (owner n)).carrier)
    (testedLocal designatedLocal : Q → HypergraphPiece W → Prop)
    (hOld :
      ∀ q,
        ForestCompletionProperty
          (testedLocal q) (designatedLocal q) m)
    (hTestSelected :
      ∀ n : N, testedLocal (owner n) (selectedGlobal n))
    (hTestOneEdge :
      ∀ q (e : Set W), e ∈ (P q).edges →
        testedLocal q (HypergraphPiece.oneEdge e))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → R.carrier ⊆ (P q).carrier)
    (hDesignatedGlobal :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → designated R) :
    ∃ (K : Q → Type v),
      ∃ (finite : ∀ q, Fintype (K q)),
        letI : ∀ q, Fintype (K q) := finite
        ∃ (family : (q : Q) → K q → HypergraphPiece W),
        ∃ keep : Finset (Sigma K),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma K // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  have hChoice (q : Q) (r : JOuter.tree.neighborSet q) :
      ∃ e : Set W, e ∈ (P q).edges ∧
        (P q).carrier ∩ (P r.1).carrier ⊆ e :=
    exists_support_edge_covering_separator
      hOuter hNonempty hVertexCover r.2.ne.symm
  let separatorEdge :
      (q : Q) → JOuter.tree.neighborSet q → Set W :=
    fun q r => Classical.choose (hChoice q r)
  have hSeparatorSpec (q : Q) (r : JOuter.tree.neighborSet q) :
      separatorEdge q r ∈ (P q).edges ∧
        (P q).carrier ∩ (P r.1).carrier ⊆
          separatorEdge q r :=
    Classical.choose_spec (hChoice q r)
  let requested :
      (q : Q) →
        ({n : N // owner n = q} ⊕ JOuter.tree.neighborSet q) →
          HypergraphPiece W :=
    fun q =>
      Sum.elim
        (fun n => selectedGlobal n.1)
        (fun r => HypergraphPiece.oneEdge (separatorEdge q r))
  have hSelectedRequest :
      ∀ q (n : {n : N // owner n = q}),
        requested q (.inl n) = selectedGlobal n.1 := by
    intro q n
    rfl
  have hRequestContained :
      ∀ q (r : {n : N // owner n = q} ⊕
        JOuter.tree.neighborSet q),
        (requested q r).carrier ⊆ (P q).carrier := by
    intro q r
    cases r with
    | inl n =>
        change (selectedGlobal n.1).carrier ⊆ (P q).carrier
        have h := hSelectedContained n.1
        rw [n.2] at h
        exact h
    | inr r =>
        change separatorEdge q r ⊆ (P q).carrier
        exact (P q).edge_subset (hSeparatorSpec q r).1
  have hConnectorOneEdge :
      ∀ q (r : JOuter.tree.neighborSet q),
        (requested q (.inr r)).IsOneEdge := by
    intro q r
    exact HypergraphPiece.oneEdge_isOneEdge _
  have hSeparator :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        (P q).carrier ∩ (P r).carrier ⊆
          (requested q (.inr ⟨r, hadj⟩)).carrier := by
    intro q r hadj
    exact (hSeparatorSpec q ⟨r, hadj⟩).2
  have hSeparatorExact :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (requested q (.inr ⟨r, hadj⟩)).carrier =
            (P q).carrier ∩ (P r).carrier := by
    intro q r hadj hBig
    exact separator_edge_exact_of_ambient_girth
      hOuter hEdges hGirth hadj.ne.symm
      (hSeparatorSpec q ⟨r, hadj⟩).1
      (hSeparatorSpec q ⟨r, hadj⟩).2 hBig
  have hTest :
      ∀ q (r : {n : N // owner n = q} ⊕
        JOuter.tree.neighborSet q),
        testedLocal q (requested q r) := by
    intro q r
    cases r with
    | inl n =>
        change testedLocal q (selectedGlobal n.1)
        have h := hTestSelected n.1
        rw [n.2] at h
        exact h
    | inr r =>
        exact hTestOneEdge q (separatorEdge q r)
          (hSeparatorSpec q r).1
  exact
    ForestCompletionProperty.assemble_over_joinTree
      hOuter JOuter hEdges hGirth
      owner hSurj m hCard selectedGlobal requested
      hSelectedRequest hRequestContained
      hConnectorOneEdge hSeparator hSeparatorExact
      testedLocal designatedLocal hOld hTest
      designated hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
