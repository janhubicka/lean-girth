import Girth.LocalForestCompletionBridge
import Girth.ForestCompletionProperty

/-! # Transport the old forest-completion invariant to each standard copy

The circulation induction assumes a *single* completion property in the old
picture. Its standard embeddings transport that quantified property into
every owner picture. The transported owner-local completions can then be
assembled along the local strong-support forest.

This theorem removes the independent owner-by-owner completion assumption.
What remains is the concrete active-picture verification that every tested
piece in each standard copy has an old tested preimage, and that designated
old pieces are transported to designated new pieces.
-/

namespace StructuralRamsey.Girth

universe v
variable {X W Q N : Type v}

/-- Old quantified finite completion, together with support-forest geometry
and transport-compatible tested/designated predicates, produces one global
designated completion of the selected pieces. -/
theorem ForestCompletionProperty.assemble_transported_strongSupportForest
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {H : Set (Set X)} {K : Set (Set W)}
    (hH : H.Nonempty)
    (hSourceCover :
      ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (hTargetGirth : GirthGT K 2)
    (outer : Q → StrongSupportEmbedding H K)
    (hForest :
      ForestOfCopies (fun q : Q => (outer q).supportPiece))
    (owner : N → Q)
    (hSurj : Function.Surjective owner)
    (m : ℕ)
    (hCard : Fintype.card N ≤ m)
    (selectedGlobal : N → HypergraphPiece W)
    (hSelectedContained :
      ∀ n : N, (selectedGlobal n).carrier ⊆
        (outer (owner n)).supportPiece.carrier)
    (testedOld designatedOld : HypergraphPiece X → Prop)
    (hOld :
      ForestCompletionProperty testedOld designatedOld m)
    (standard : Q → X ↪ W)
    (testedLocal designatedLocal : Q → HypergraphPiece W → Prop)
    (hTestPullback :
      ∀ q (T : HypergraphPiece W),
        testedLocal q T →
          ∃ S : HypergraphPiece X,
            testedOld S ∧ T = S.map (standard q))
    (hDesignatedTransport :
      ∀ q (S : HypergraphPiece X),
        designatedOld S →
          designatedLocal q (S.map (standard q)))
    (hTestSelected :
      ∀ n : N, testedLocal (owner n) (selectedGlobal n))
    (hTestOneEdge :
      ∀ q (e : Set W),
        e ∈ (outer q).supportPiece.edges →
          testedLocal q (HypergraphPiece.oneEdge e))
    (designated : HypergraphPiece W → Prop)
    (hDesignatedContained :
      ∀ q (R : HypergraphPiece W),
        designatedLocal q R →
          R.carrier ⊆ (outer q).supportPiece.carrier)
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
      hH hSourceCover hTargetGirth outer hForest
      owner hSurj m hCard selectedGlobal hSelectedContained
      testedLocal designatedLocal hLocal
      hTestSelected hTestOneEdge
      designated hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
