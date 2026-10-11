import Girth.ForestCanonicalMixedIncrement
import Girth.ForestGluingSourceCoverage
import Girth.ForestCanonicalTransport

/-!
# Direct forest increment from one old q-forest and actual gluing factorization

The conditional forest increment previously took three independent-looking
small-gluing hypotheses: every gluing support is nonempty, each of its
vertices lies in one support edge, and its one-edge connector pieces are
tested old-picture pieces. In the actual induced partite construction,
the gluing copies are images of ONE nonempty A-generated active support
under strong embeddings that factor through their standard pictures.

Source nonemptiness and vertex coverage therefore give the first two
conditions. Factorization plus testing of old A-support edges gives the
third, by the verified exact one-edge transport theorem.

Combining these reductions with canonical q-forest transport leaves:
actual source generation, honest small/full/core geometry and local girth,
the preceding mixed (q-1)-forest invariant, ONE old q-forest invariant,
and actual regular/exceptional selected A/B support certificates.
It does NOT prove the recursive train Ramsey witness exists.
-/

namespace StructuralRamsey.Girth

universe v
variable {Src Old W Q E N : Type v}

/-- Under genuine gluing factorization and A-generated source coverage,
the selected mixed family is a forest. No separate small-gluing
vertex-coverage, nonemptiness, or connector old-test premises. -/
theorem selectedForest_of_factoredCanonicalMixedCases
    [Fintype N] [Nonempty N]
    {H : Set (Set Src)} {K : Set (Set W)}
    (outer : Q → StrongSupportEmbedding H K)
    (active : Q → Src ↪ Old)
    (standard : Q → Old ↪ W)
    (hFactor : ∀ i x, outer i x = standard i (active i x))
    (hSourceNonempty : H.Nonempty)
    (hSourceCover :
      ∀ x : Src, ∃ e : Set Src, e ∈ H ∧ x ∈ e)
    (full : Q → HypergraphPiece W)
    (hFullCarrier : ∀ i, (full i).carrier = Set.range (standard i))
    (S : Set W) [Fintype S]
    (hRangeCore : ∀ i, Set.range (outer i) ⊆ S)
    (coreEdge : E → Set W)
    (selected : N → HypergraphPiece W)
    (hSelectedInj : Function.Injective selected)
    (m : ℕ) (hm : 2 ≤ m)
    (hCount : Fintype.card N ≤ m)
    (hPrevious :
      LocalForestThrough
        (mixedOwnerSmall (fun i => (outer i).supportPiece) coreEdge)
        (m - 1))
    (hRegularSub :
      ∀ i : Q, (outer i).supportPiece.carrier ⊆ (full i).carrier)
    (hRegularEdges :
      ∀ i : Q, (outer i).supportPiece.edges ⊆ (full i).edges)
    (hRegularOverlap :
      ∀ ⦃i j : Q⦄, i ≠ j →
        (full i).carrier ∩ (full j).carrier =
          (outer i).supportPiece.carrier ∩
            (outer j).supportPiece.carrier)
    (hFullCore : ∀ i : Q,
      (full i).carrier ∩ S = (outer i).supportPiece.carrier)
    (hCoreEdgeLocal : ∀ e : E, coreEdge e ∈ K)
    (hCoreEdgeSub : ∀ e : E, coreEdge e ⊆ S)
    (hGirth : GirthGT K m)
    {Ambient : Set (Set W)}
    (hRegularAmbient :
      ∀ i : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full i).edges → e ∈ Ambient)
    (hCoreAmbient : ∀ i : E, coreEdge i ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (testedOld : HypergraphPiece Old → Prop)
    (hOld : FiniteMixedForestThrough testedOld m)
    (hOldActiveEdge :
      ∀ i (e : Set Src), e ∈ H →
        testedOld (HypergraphPiece.oneEdge ((active i) '' e)))
    (hCases : ∀ n : N,
      (∃ i : Q,
        TransportedPiece testedOld (standard i) (selected n) ∧
          SmallOrWholeEdgeBoundary K S (selected n)) ∨
      (∃ e : E,
        selected n = HypergraphPiece.oneEdge (coreEdge e))) :
    ForestOfCopies selected := by
  have hSmallNonempty : ∀ i : Q,
      (outer i).supportPiece.edges.Nonempty :=
    fun i => (outer i).supportPiece_edgesNonempty hSourceNonempty
  have hSmallCovered : ∀ i : Q, ∀ x : W,
      x ∈ (outer i).supportPiece.carrier →
        ∃ e : Set W, e ∈ (outer i).supportPiece.edges ∧ x ∈ e :=
    fun i => (outer i).supportPiece_vertexCovered hSourceCover
  have hSmallCore : ∀ i : Q,
      (outer i).supportPiece.carrier ⊆ S :=
    fun i => (outer i).supportPiece_carrier_subset_core S (hRangeCore i)
  have hConnectors : ∀ i : Q, ∀ (e : Set W),
      e ∈ (outer i).supportPiece.edges →
      TransportedPiece testedOld (standard i)
        (HypergraphPiece.oneEdge e) :=
    allGluingOneEdges_transported_of_factor
      outer active standard hFactor testedOld hOldActiveEdge
  exact selectedForest_of_canonicalMixedCases
    (fun i => (outer i).supportPiece) full standard hFullCarrier
    S coreEdge selected hSelectedInj m hm hCount hPrevious
    hRegularSub hRegularEdges hRegularOverlap hFullCore
    hSmallNonempty hSmallCovered hSmallCore K
    hCoreEdgeLocal hCoreEdgeSub hGirth
    hRegularAmbient hCoreAmbient hAmbientGirth
    testedOld hOld hConnectors hCases

end StructuralRamsey.Girth
