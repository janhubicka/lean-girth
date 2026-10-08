import Girth.ForestCompletionSupportedBridge
import Girth.LocalForestPieces

/-! # Forest completion for a family of strong support embeddings

A local forest witness is presented as a family of strong embeddings between
support hypergraphs. The support pieces of these embeddings have nonempty edge
families, and their carriers are covered by their support edges, whenever the
source hypergraph has these properties.

These facts make the one-edge separator construction automatic and feed the
complete quantified owner-local completion bridge. The remaining hypotheses
are exactly the choice of tested members in the corresponding old standard
pictures, and the transport of designated completed members.
-/

namespace StructuralRamsey.Girth

universe v
variable {X W Q N : Type v}

namespace StrongSupportEmbedding

variable {H : Set (Set X)} {K : Set (Set W)}

/-- A strong image of a nonempty support hypergraph is a piece with at least
one support edge. -/
theorem supportPiece_edges_nonempty
    (f : StrongSupportEmbedding H K)
    (hH : H.Nonempty) :
    f.supportPiece.edges.Nonempty := by
  rcases hH with ⟨e, he⟩
  exact ⟨f '' e, ⟨e, he, rfl⟩⟩

/-- If all source vertices lie in source support edges, the same is true of
the carrier and edge family of each strong support image piece. -/
theorem supportPiece_vertex_covered
    (f : StrongSupportEmbedding H K)
    (hCover : ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
    (y : W)
    (hy : y ∈ f.supportPiece.carrier) :
    ∃ e : Set W, e ∈ f.supportPiece.edges ∧ y ∈ e := by
  change y ∈ Set.range f at hy
  rcases hy with ⟨x, rfl⟩
  obtain ⟨e, he, hx⟩ := hCover x
  exact ⟨f '' e, ⟨e, he, rfl⟩, ⟨x, hx, rfl⟩⟩

end StrongSupportEmbedding

/-- The quantified local completion property assembles over any finite forest
of selected strong support copies. No independent connector or separator
existence hypotheses are necessary: the source support coverage and ambient
target girth provide one-edge connector requests.

The tested-member and designated-copy compatibility assumptions remain
visible, as they are precisely the input provided by the active picture step. -/
theorem ForestCompletionProperty.assemble_over_strongSupportForest
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
    (testedLocal designatedLocal :
      Q → HypergraphPiece W → Prop)
    (hOld :
      ∀ q,
        ForestCompletionProperty
          (testedLocal q) (designatedLocal q) m)
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
  let P : Q → HypergraphPiece W :=
    fun q => (outer q).supportPiece
  have hFP : ForestOfCopies P := hForest
  let J : JoinTree P :=
    Classical.choice hFP.joinTree_of_nonempty
  have hEdges :
      ∀ q : Q, ∀ ⦃e : Set W⦄,
        e ∈ (P q).edges → e ∈ K := by
    intro q e he
    exact (outer q).supportPiece_edges_in_target he
  have hNonempty : ∀ q, (P q).edges.Nonempty := by
    intro q
    exact (outer q).supportPiece_edges_nonempty hH
  have hVertexCovered :
      ∀ q (x : W), x ∈ (P q).carrier →
        ∃ e : Set W, e ∈ (P q).edges ∧ x ∈ e := by
    intro q x hx
    exact (outer q).supportPiece_vertex_covered hSourceCover x hx
  exact
    ForestCompletionProperty.assemble_over_joinTree_of_supported_separators
      hFP.pairwiseAllowed J hEdges hTargetGirth
      hNonempty hVertexCovered
      owner hSurj m hCard selectedGlobal
      hSelectedContained
      testedLocal designatedLocal hOld
      hTestSelected hTestOneEdge
      designated hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
