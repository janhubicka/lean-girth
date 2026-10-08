import Girth.LocalForestCompletionBridge
import Girth.ForestCompletionProperty

/-! # Transport the old completion invariant through full standard pictures

The source support hypergraph of the local gluing copies may be the *active*
subsystem, which is smaller than the old full picture. We distinguish these
two old vertex types. The local strong-support embeddings use the active
subsystem, while the full standard embeddings transport the forest-completion
invariant of the *whole* old picture.

Together with the two-carrier join-tree assembly this derives owner-local
completions from the single induction hypothesis.
-/

namespace StructuralRamsey.Girth

universe v
variable {Src Old W Q N : Type v}

/-- A single old completion property, transported into each full standard
copy, gives a global designated completion. Small gluing carriers supply
separators; the full standard copies contain the completed designated pieces.

The remaining inputs are the concrete pullback of tested pieces, the
transport of designated B-pieces, and the geometry relating the two carriers
in the standard attachment. -/
theorem ForestCompletionProperty.assemble_transported_strongSupportForest
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {H : Set (Set Src)} {K Ambient : Set (Set W)}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (outer : Q → StrongSupportEmbedding H K)
    (full : Q → HypergraphPiece W)
    (hInnerForest :
      ForestOfCopies (fun q : Q => (outer q).supportPiece))
    (hSmallSub :
      ∀ q : Q,
        (outer q).supportPiece.carrier ⊆ (full q).carrier)
    (hPair :
      ∀ ⦃q r : Q⦄, q ≠ r →
        (full q).carrier ∩ (full r).carrier =
          (outer q).supportPiece.carrier ∩
            (outer r).supportPiece.carrier)
    (hSmallEdges :
      ∀ q : Q,
        (outer q).supportPiece.edges ⊆ (full q).edges)
    (hFullEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full q).edges → e ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (hSelectedContained :
      ∀ n : N, (selectedGlobal n).carrier ⊆
        (full (owner n)).carrier)
    (testedOld designatedOld : HypergraphPiece Old → Prop)
    (hOld :
      ForestCompletionProperty testedOld designatedOld m)
    (standard : Q → Old ↪ W)
    (testedLocal designatedLocal : Q → HypergraphPiece W → Prop)
    (hTestPullback :
      ∀ q (T : HypergraphPiece W),
        testedLocal q T →
          ∃ S : HypergraphPiece Old,
            testedOld S ∧ T = S.map (standard q))
    (hDesignatedTransport :
      ∀ q (S : HypergraphPiece Old),
        designatedOld S →
          designatedLocal q (S.map (standard q)))
    (hTestSelected :
      ∀ n : N, testedLocal (owner n) (selectedGlobal n))
    (hTestOneEdge :
      ∀ q (e : Set W), e ∈ (outer q).supportPiece.edges →
        testedLocal q (HypergraphPiece.oneEdge e))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R →
          R.carrier ⊆ (full q).carrier)
    (hDesignatedGlobal :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R → designated R) :
    ∃ (T : Q → Type v),
      ∃ (finite : ∀ q, Fintype (T q)),
        letI : ∀ q, Fintype (T q) := finite
        ∃ (family : (q : Q) → T q → HypergraphPiece W),
        ∃ keep : Finset (Sigma T),
          ForestCompletionWitness selectedGlobal designated
            (fun z : {z : Sigma T // z ∈ keep} =>
              family z.1.1 z.1.2) := by
  classical
  have hLocal (q : Q) :
      ForestCompletionProperty
        (testedLocal q) (designatedLocal q) m :=
    ForestCompletionProperty.map
      hOld (standard q)
      (testedLocal q) (designatedLocal q)
      (hTestPullback q) (hDesignatedTransport q)
  exact
    ForestCompletionProperty.assemble_over_strongSupportForest
      hSourceNonempty hSourceCover outer full
      hInnerForest hSmallSub hPair hSmallEdges
      hFullEdges hAmbientGirth
      owner hSurj m hCard
      selectedGlobal hSelectedContained
      testedLocal designatedLocal hLocal
      hTestSelected hTestOneEdge
      designated hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
