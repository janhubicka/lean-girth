import Girth.ForestCompletionTwoCarrier
import Girth.LocalForestPieces

/-! # Completing full standard copies using their small strong-support cores

The small gluing pieces are images of strong support embeddings in the local
partite Ramsey witness. The full standard-picture pieces contain them and
have the same pairwise intersections, but may also contain private vertices
and transported designated B-copies.

Only the small pieces need support-edge coverage: they supply the one-edge
separator requests. The full pieces are used to contain selected and completed
designated copies. This is the correct two-carrier form for the circulation
proof.
-/

namespace StructuralRamsey.Girth

universe v
variable {X W Q N : Type v}

namespace StrongSupportEmbedding

variable {H : Set (Set X)} {K : Set (Set W)}

/-- A strong image of a nonempty support hypergraph has a support edge. -/
theorem supportPiece_edges_nonempty
    (f : StrongSupportEmbedding H K)
    (hH : H.Nonempty) :
    f.supportPiece.edges.Nonempty := by
  rcases hH with ⟨e, he⟩
  exact ⟨f '' e, ⟨e, he, rfl⟩⟩

/-- Every vertex of a strong-support image lies in an image support edge,
provided all source vertices belong to source support edges. -/
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

/-- Choose and assemble per-owner completions using a forest of strong
support copies as the gluing pieces and full standard-picture pieces as the
ambient containers of designated completions. Support coverage and ambient
girth construct the separator requests automatically. -/
theorem ForestCompletionProperty.assemble_over_strongSupportForest
    [Fintype Q] [Nonempty Q] [DecidableEq Q] [Fintype N]
    {H : Set (Set X)} {K Ambient : Set (Set W)}
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : X, ∃ e : Set X, e ∈ H ∧ x ∈ e)
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
      ∀ n : N,
        (selectedGlobal n).carrier ⊆
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
  let small : Q → HypergraphPiece W :=
    fun q => (outer q).supportPiece
  have hSmallNonempty :
      ∀ q, (small q).edges.Nonempty := by
    intro q
    exact (outer q).supportPiece_edges_nonempty hSourceNonempty
  have hSmallVertexCover :
      ∀ q (x : W), x ∈ (small q).carrier →
        ∃ e : Set W, e ∈ (small q).edges ∧ x ∈ e := by
    intro q x hx
    exact (outer q).supportPiece_vertex_covered hSourceCover x hx
  exact
    ForestCompletionProperty.assemble_over_two_carrier_joinTree
      hInnerForest hSmallSub hPair hSmallEdges
      hFullEdges hAmbientGirth
      hSmallNonempty hSmallVertexCover
      owner hSurj m hCard selectedGlobal hSelectedContained
      testedLocal designatedLocal hOld
      hTestSelected hTestOneEdge
      designated hDesignatedContained hDesignatedGlobal

end StructuralRamsey.Girth
