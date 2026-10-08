import Girth.ForestCompletionSeparatorRequests
import Girth.ForestOverlapTransfer

/-! # Completion assembly across small gluing and full standard-picture pieces

The local forest lives on the small glued support copies, but selected and
designated B-copies can extend into private vertices of full standard
pictures. Treating these carriers as equal is incorrect.

The correct geometry has TWO families: a small support forest and a family
of full standard-picture pieces. Each small carrier embeds into its full
carrier, pairwise intersections are unchanged, and small support edges
remain edges of the full pieces. The small family supplies separator edges;
the full family contains all completed designated pieces. The same outer
join tree controls both families.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q N : Type v}

/-- Complete a finite selected family using owner-local completion invariants
and a forest of *small* gluing pieces inside full standard-picture pieces.
Every separator request is chosen from the small support family, whereas the
completed designated pieces need only lie in their corresponding full pieces.

Ambient girth ensures both full-copy support linearity and the exactness of a
chosen separator edge when the overlap has at least two vertices. -/
theorem ForestCompletionProperty.assemble_over_two_carrier_joinTree
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {small full : Q → HypergraphPiece W}
    (hSmallForest : ForestOfCopies small)
    (hSmallSub :
      ∀ q : Q, (small q).carrier ⊆ (full q).carrier)
    (hPair :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (full q).carrier ∩ (full r).carrier =
          (small q).carrier ∩ (small r).carrier)
    (hSmallEdges :
      ∀ q : Q, (small q).edges ⊆ (full q).edges)
    {H : Set (Set W)}
    (hFullEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full q).edges → e ∈ H)
    (hGirth : GirthGT H 2)
    (hSmallNonempty :
      ∀ q, (small q).edges.Nonempty)
    (hSmallVertexCover :
      ∀ q (x : W), x ∈ (small q).carrier →
        ∃ e : Set W, e ∈ (small q).edges ∧ x ∈ e)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (hSelectedContained :
      ∀ n : N, (selectedGlobal n).carrier ⊆
        (full (owner n)).carrier)
    (testedLocal designatedLocal :
      Q → HypergraphPiece W → Prop)
    (hOld :
      ∀ q,
        ForestCompletionProperty
          (testedLocal q) (designatedLocal q) m)
    (hTestSelected :
      ∀ n : N, testedLocal (owner n) (selectedGlobal n))
    (hTestOneEdge :
      ∀ q (e : Set W), e ∈ (small q).edges →
        testedLocal q (HypergraphPiece.oneEdge e))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R →
          R.carrier ⊆ (full q).carrier)
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
  let JSmall : JoinTree small :=
    Classical.choice hSmallForest.joinTree_of_nonempty
  let JFull : JoinTree full :=
    JSmall.transfer_of_pair_intersections hSmallSub hPair
  have hFullForest : ForestOfCopies full :=
    hSmallForest.transfer_of_pair_intersections
      hSmallSub hPair hSmallEdges
  have hSmallEdgesAmbient :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (small q).edges → e ∈ H := by
    intro q e he
    exact hFullEdges q (hSmallEdges q he)
  have hChoice (q : Q) (r : JFull.tree.neighborSet q) :
      ∃ e : Set W, e ∈ (small q).edges ∧
        (small q).carrier ∩ (small r.1).carrier ⊆ e :=
    exists_support_edge_covering_separator
      hSmallForest.pairwiseAllowed
      hSmallNonempty hSmallVertexCover r.2.ne
  let separatorEdge :
      (q : Q) → JFull.tree.neighborSet q → Set W :=
    fun q r => Classical.choose (hChoice q r)
  have hSeparatorSpec
      (q : Q) (r : JFull.tree.neighborSet q) :
      separatorEdge q r ∈ (small q).edges ∧
        (small q).carrier ∩ (small r.1).carrier ⊆
          separatorEdge q r :=
    Classical.choose_spec (hChoice q r)
  let requested :
      (q : Q) →
        ({n : N // owner n = q} ⊕
          JFull.tree.neighborSet q) → HypergraphPiece W :=
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
        JFull.tree.neighborSet q),
        (requested q r).carrier ⊆ (full q).carrier := by
    intro q r
    cases r with
    | inl n =>
        change (selectedGlobal n.1).carrier ⊆
          (full q).carrier
        have h := hSelectedContained n.1
        rw [n.2] at h
        exact h
    | inr r =>
        change separatorEdge q r ⊆ (full q).carrier
        exact
          (full q).edge_subset
            (hSmallEdges q (hSeparatorSpec q r).1)
  have hConnectorOneEdge :
      ∀ q (r : JFull.tree.neighborSet q),
        (requested q (.inr r)).IsOneEdge := by
    intro q r
    exact HypergraphPiece.oneEdge_isOneEdge _
  have hSeparator :
      ∀ ⦃q r : Q⦄ (hadj : JFull.tree.Adj q r),
        (full q).carrier ∩ (full r).carrier ⊆
          (requested q (.inr ⟨r, hadj⟩)).carrier := by
    intro q r hadj
    change
      (full q).carrier ∩ (full r).carrier ⊆
        separatorEdge q ⟨r, hadj⟩
    rw [hPair hadj.ne]
    exact (hSeparatorSpec q ⟨r, hadj⟩).2
  have hSeparatorExact :
      ∀ ⦃q r : Q⦄ (hadj : JFull.tree.Adj q r),
        ¬((full q).carrier ∩ (full r).carrier).Subsingleton →
          (requested q (.inr ⟨r, hadj⟩)).carrier =
            (full q).carrier ∩ (full r).carrier := by
    intro q r hadj hBig
    have hBigSmall :
        ¬((small q).carrier ∩ (small r).carrier).Subsingleton := by
      rw [← hPair hadj.ne]
      exact hBig
    have hExact :=
      separator_edge_exact_of_ambient_girth
        hSmallForest.pairwiseAllowed
        hSmallEdgesAmbient hGirth hadj.ne
        (hSeparatorSpec q ⟨r, hadj⟩).1
        (hSeparatorSpec q ⟨r, hadj⟩).2 hBigSmall
    change separatorEdge q ⟨r, hadj⟩ =
      (full q).carrier ∩ (full r).carrier
    rw [hPair hadj.ne]
    exact hExact
  have hTest :
      ∀ q (r : {n : N // owner n = q} ⊕
        JFull.tree.neighborSet q),
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
      hFullForest.pairwiseAllowed JFull
      hFullEdges hGirth
      owner hSurj m hCard selectedGlobal requested
      hSelectedRequest hRequestContained
      hConnectorOneEdge hSeparator hSeparatorExact
      testedLocal designatedLocal hOld hTest
      designated hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
