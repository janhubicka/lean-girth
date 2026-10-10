import Girth.ForestMixedRequestJoin
import Girth.ForestSmallSeparatorChoice
import Girth.ForestRepeatedOwnerOuter
import Girth.ForestCompletionGirthBridge

/-!
# Complete abstract repeated-owner branch of the direct forest increment

When selected members repeat a containing standard-picture owner,
there are at most q-1 used local gluing copies. Their bounded local
forest transfers to full standard pictures. The vertex-covered SMALL
gluing supports choose genuine old A-edge separator requests.
The old picture's mixed forest property through q then supplies
the DISTINCT local request set forest, and the join-tree lift reuses
connector labels rather than duplicating them. Remove only
unselected one-edge separator pieces.

No false full-picture vertex coverage and no arbitrary subfamily
heredity. The actual picture-step must still supply the honest
factorization, tested support membership and local Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {W N I : Type v}

/-- The abstract repeated-owner forest increment, using only
the previous local forest bound, the OLD mixed q-bound, and
small/full support geometry. -/
theorem selectedForest_of_repeatedOwners_mixed
    [Fintype N] [Nonempty N]
    (owner : N → I)
    (hNoninj : ¬ Function.Injective owner)
    (small full : I → HypergraphPiece W)
    (q : ℕ) (hCount : Fintype.card N ≤ q)
    (hPrevious : LocalForestThrough small (q - 1))
    (hSmallSub :
      ∀ i, (small i).carrier ⊆ (full i).carrier)
    (hSmallEdges :
      ∀ i, (small i).edges ⊆ (full i).edges)
    (hPair :
      ∀ ⦃i j : I⦄, i ≠ j →
        (full i).carrier ∩ (full j).carrier =
          (small i).carrier ∩ (small j).carrier)
    (hSmallNonempty :
      ∀ i, (small i).edges.Nonempty)
    (hSmallVertexCovered :
      ∀ i (x : W), x ∈ (small i).carrier →
        ∃ e : Set W, e ∈ (small i).edges ∧ x ∈ e)
    {Ambient : Set (Set W)}
    (hFullEdgesAmbient :
      ∀ i : I, ∀ ⦃e : Set W⦄,
        e ∈ (full i).edges → e ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (selected : N → HypergraphPiece W)
    (hSelectedInj : Function.Injective selected)
    (hSelectedContain :
      ∀ n, (selected n).carrier ⊆ (full (owner n)).carrier)
    (tested : I → HypergraphPiece W → Prop)
    (hOld :
      ∀ i, FiniteMixedForestThrough (tested i) q)
    (hSelectedTest :
      ∀ n, tested (owner n) (selected n))
    (hSmallEdgeTest :
      ∀ i (e : Set W), e ∈ (small i).edges →
        tested i (HypergraphPiece.oneEdge e)) :
    ForestOfCopies selected := by
  classical
  let Q := UsedOwner owner
  letI : Fintype Q := usedOwnerFintype owner
  letI : Nonempty Q := usedOwner_nonempty owner
  letI : DecidableEq Q := Classical.decEq _
  let smallU : Q → HypergraphPiece W := fun u => small u.1
  let fullU : Q → HypergraphPiece W := fun u => full u.1
  have hSmallForest : ForestOfCopies smallU :=
    localForest_repeatedOwners owner small q
      hCount hNoninj hPrevious
  have hFullForest : ForestOfCopies fullU :=
    fullStandardForest_repeatedOwners owner small full q
      hCount hNoninj hPrevious hSmallSub hSmallEdges hPair
  let JSmall : JoinTree smallU :=
    Classical.choice hSmallForest.joinTree_of_nonempty
  have hSubU :
      ∀ u : Q, (smallU u).carrier ⊆ (fullU u).carrier :=
    fun u => hSmallSub u.1
  have hPairU :
      ∀ ⦃u v : Q⦄, u ≠ v →
        (fullU u).carrier ∩ (fullU v).carrier =
          (smallU u).carrier ∩ (smallU v).carrier := by
    intro u v huv
    apply hPair
    intro heq
    exact huv (Subtype.ext heq)
  let JFull : JoinTree fullU :=
    JSmall.transfer_of_pair_intersections hSubU hPairU
  have hSmallEdgesU :
      ∀ u : Q, (smallU u).edges ⊆ (fullU u).edges :=
    fun u => hSmallEdges u.1
  have hSmallNonemptyU :
      ∀ u : Q, (smallU u).edges.Nonempty :=
    fun u => hSmallNonempty u.1
  have hSmallCoveredU :
      ∀ u (x : W), x ∈ (smallU u).carrier →
        ∃ e : Set W, e ∈ (smallU u).edges ∧ x ∈ e :=
    fun u => hSmallVertexCovered u.1
  have hFullAmbientU :
      ∀ u : Q, ∀ ⦃e : Set W⦄,
        e ∈ (fullU u).edges → e ∈ Ambient :=
    fun u => hFullEdgesAmbient u.1
  obtain ⟨edge, hEdge⟩ :=
    exists_smallSupport_separatorEdges
      hSmallForest JSmall hPairU hSmallEdgesU
      hSmallNonemptyU hSmallCoveredU
      hFullAmbientU hAmbientGirth
  let separator :
      (u : Q) → JFull.tree.neighborSet u → HypergraphPiece W :=
    fun u r => HypergraphPiece.oneEdge (edge u r)
  have hSeparatorTest :
      ∀ u (r : JFull.tree.neighborSet u),
        tested u.1 (separator u r) := by
    intro u r
    exact hSmallEdgeTest u.1 (edge u r) (hEdge u r).1
  have hSeparatorContain :
      ∀ u (r : JFull.tree.neighborSet u),
        (separator u r).carrier ⊆ (fullU u).carrier := by
    intro u r
    exact (hEdge u r).2.1
  have hSeparatorOneEdge :
      ∀ u (r : JFull.tree.neighborSet u),
        (separator u r).IsOneEdge := by
    intro u r
    rfl
  have hSeparatorCover :
      ∀ ⦃u v : Q⦄ (hadj : JFull.tree.Adj u v),
        (fullU u).carrier ∩ (fullU v).carrier ⊆
          (separator u ⟨v, hadj⟩).carrier := by
    intro u v hadj
    exact (hEdge u ⟨v, hadj⟩).2.2.1
  have hSeparatorExact :
      ∀ ⦃u v : Q⦄ (hadj : JFull.tree.Adj u v),
        ¬((fullU u).carrier ∩ (fullU v).carrier).Subsingleton →
          (separator u ⟨v, hadj⟩).carrier =
            (fullU u).carrier ∩ (fullU v).carrier := by
    intro u v hadj hBig
    exact (hEdge u ⟨v, hadj⟩).2.2.2 hBig
  have hLinear : OuterEdgesLinear fullU :=
    outerEdgesLinear_of_ambient_girth
      hFullAmbientU hAmbientGirth
  let ownerU : N → Q := usedOwnerMap owner
  have hSelectedContainU :
      ∀ n, (selected n).carrier ⊆
        (fullU (ownerU n)).carrier :=
    hSelectedContain
  let testedU : Q → HypergraphPiece W → Prop :=
    fun u T => tested u.1 T
  have hOldU :
      ∀ u, FiniteMixedForestThrough (testedU u) q :=
    fun u => hOld u.1
  have hSelectedTestU :
      ∀ n, testedU (ownerU n) (selected n) :=
    hSelectedTest
  exact selectedForest_of_mixedRequestJoin
    hFullForest.pairwiseAllowed JFull hLinear
    ownerU (usedOwnerMap_surjective owner)
    selected hSelectedInj separator q hCount
    testedU hOldU hSelectedTestU hSeparatorTest
    hSelectedContainU hSeparatorContain
    hSeparatorOneEdge hSeparatorCover hSeparatorExact

end StructuralRamsey.Girth
