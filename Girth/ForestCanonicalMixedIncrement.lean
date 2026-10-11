import Girth.ForestCanonicalMixedForestTransport
import Girth.ForestCanonicalMixedOwnerCases

/-!
# Canonical old-picture forests give the direct mixed forest increment

The previous-picture q-forest invariant is ONE finite set-valued
statement about old tested A/B support pieces. Every standard copy's
tested family is exactly its canonical image under the standard
embedding, so the local q-forest predicates are NOT independent
hypotheses: they all follow by injective transport.

Likewise, a selected finite mixed family does not require a separately
chosen owner function. Actual regular/exceptional classification
certificates (tested canonical standard image with legal boundary, or
literal core edge) supply that function and its necessary properties.

This short composition reduces the conditional direct picture
increment to the genuine local previous-cutoff mixed forest bound,
core/outer geometry, the ONE old q-forest bound, and actual selected
A/B case classification. It does not construct a recursive Ramsey
witness or assert the global circulation theorem.
-/

namespace StructuralRamsey.Girth

universe v
variable {Old W Q E N : Type v}

/-- Finite selected mixed supports form a forest using just the
ONE old-picture finite mixed q-forest invariant and genuine canonical
regular/exceptional cases. No per-standard-picture q-forest axiom
and no independently supplied owner assignment. -/
theorem selectedForest_of_canonicalMixedCases
    [Fintype N] [Nonempty N]
    (small full : Q → HypergraphPiece W)
    (standard : Q → Old ↪ W)
    (hFullCarrier : ∀ q, (full q).carrier = Set.range (standard q))
    (S : Set W) [Fintype S]
    (coreEdge : E → Set W)
    (selected : N → HypergraphPiece W)
    (hSelectedInj : Function.Injective selected)
    (q : ℕ) (hq : 2 ≤ q)
    (hCount : Fintype.card N ≤ q)
    (hPrevious :
      LocalForestThrough (mixedOwnerSmall small coreEdge) (q - 1))
    (hRegularSub :
      ∀ i : Q, (small i).carrier ⊆ (full i).carrier)
    (hRegularEdges :
      ∀ i : Q, (small i).edges ⊆ (full i).edges)
    (hRegularOverlap :
      ∀ ⦃i j : Q⦄, i ≠ j →
        (full i).carrier ∩ (full j).carrier =
          (small i).carrier ∩ (small j).carrier)
    (hFullCore : ∀ i : Q,
      (full i).carrier ∩ S = (small i).carrier)
    (hSmallNonempty : ∀ i : Q, (small i).edges.Nonempty)
    (hSmallCovered : ∀ i : Q, ∀ x : W,
      x ∈ (small i).carrier →
        ∃ e : Set W, e ∈ (small i).edges ∧ x ∈ e)
    (hSmallInCore : ∀ i : Q, (small i).carrier ⊆ S)
    (K : Set (Set W))
    (hCoreEdgeLocal : ∀ e : E, coreEdge e ∈ K)
    (hCoreEdgeSub : ∀ e : E, coreEdge e ⊆ S)
    (hGirth : GirthGT K q)
    {Ambient : Set (Set W)}
    (hRegularAmbient :
      ∀ i : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full i).edges → e ∈ Ambient)
    (hCoreAmbient : ∀ i : E, coreEdge i ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (testedOld : HypergraphPiece Old → Prop)
    (hOld : FiniteMixedForestThrough testedOld q)
    (hRegularEdgeTest :
      ∀ (i : Q) (e : Set W), e ∈ (small i).edges →
        TransportedPiece testedOld (standard i)
          (HypergraphPiece.oneEdge e))
    (hCases : ∀ n : N,
      (∃ i : Q,
        TransportedPiece testedOld (standard i) (selected n) ∧
          SmallOrWholeEdgeBoundary K S (selected n)) ∨
      (∃ e : E,
        selected n = HypergraphPiece.oneEdge (coreEdge e))) :
    ForestOfCopies selected := by
  classical
  let tested : Q → HypergraphPiece W → Prop :=
    fun i T => TransportedPiece testedOld (standard i) T
  have hOldStd : ∀ i : Q,
      FiniteMixedForestThrough (tested i) q :=
    fun i => hOld.canonicalTransport testedOld (standard i) q
  have hCertified :
      ∀ n : N, ∃ o : Q ⊕ E,
        MixedOwnerSelectionCertificate (selected n)
          full coreEdge S K tested o := by
    exact mixedOwnerFamilyCases_of_canonicalTransport
      full standard hFullCarrier coreEdge S K
      testedOld selected hCases
  exact selectedForest_of_mixedOwnerClassification
    small full S coreEdge selected hSelectedInj
    q hq hCount hPrevious
    hRegularSub hRegularEdges hRegularOverlap hFullCore
    hSmallNonempty hSmallCovered hSmallInCore
    K hCoreEdgeLocal hCoreEdgeSub hGirth
    hRegularAmbient hCoreAmbient hAmbientGirth
    tested hOldStd hRegularEdgeTest hCertified

end StructuralRamsey.Girth
