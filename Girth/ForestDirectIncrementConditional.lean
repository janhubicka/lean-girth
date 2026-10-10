import Girth.ForestRepeatedOwnerMixed
import Girth.ForestDistinctOwnerTwoCarrier

/-!
# Direct forest increment: both owner cases in one theorem

There is one elementary dichotomy for a finite selected family:
the chosen full-standard picture owner map is injective, or not.
In the injective case local girth >q and exact whole-edge or
singleton core boundaries give the forest directly via the
boundary incidence tree. In the noninjective case ≤q-1 local
gluing owners give the outer forest, and the previous old-picture
mixed q-forest property supplies all distinct local request
forests for the join-tree lift.

The indexed owners may themselves include one-edge core pieces;
no duplicate connector labels,
no full-standard vertex-cover assumption, and no unrestricted
subfamily deletion.

All actual picture-step geometric premises are explicit;
this theorem does NOT construct the recursive local edge-Ramsey
witness or prove the abstract assumptions for every picture step.
-/

namespace StructuralRamsey.Girth

universe v
variable {W N I : Type v}

/-- Full abstract direct forest increment under honest small/full
picture geometry and bounded local and old mixed forest hypotheses. -/
theorem selectedForest_of_directPictureIncrement
    [Fintype N] [Nonempty N]
    (owner : N → I)
    (small full : I → HypergraphPiece W)
    (selected : N → HypergraphPiece W)
    (hSelectedInj : Function.Injective selected)
    (q : ℕ) (hq : 2 ≤ q)
    (hSelectedCard : Fintype.card N ≤ q)
    (hPrevious : LocalForestThrough small (q - 1))
    (hSmallSub :
      ∀ i, (small i).carrier ⊆ (full i).carrier)
    (hSmallEdges :
      ∀ i, (small i).edges ⊆ (full i).edges)
    (hOverlap :
      ∀ ⦃i j : I⦄, i ≠ j →
        (full i).carrier ∩ (full j).carrier =
          (small i).carrier ∩ (small j).carrier)
    (hSmallNonempty :
      ∀ i, (small i).edges.Nonempty)
    (hSmallVertexCovered :
      ∀ i (x : W), x ∈ (small i).carrier →
        ∃ e : Set W, e ∈ (small i).edges ∧ x ∈ e)
    (S : Set W) [Fintype S]
    (hSmallCore :
      ∀ i, (small i).carrier ⊆ S)
    (K : Set (Set W))
    (hLocalGirth : GirthGT K q)
    (hBoundary :
      ∀ n, SmallOrWholeEdgeBoundary K S (selected n))
    {Ambient : Set (Set W)}
    (hFullEdgesAmbient :
      ∀ i : I, ∀ ⦃e : Set W⦄,
        e ∈ (full i).edges → e ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (hSelectedContain :
      ∀ n, (selected n).carrier ⊆
        (full (owner n)).carrier)
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
  by_cases hInj : Function.Injective owner
  · exact selectedForest_of_distinctOwners_twoCarrier
      selected owner hInj small full S K q hq hSelectedCard
      hLocalGirth hOverlap hSmallCore hSelectedContain hBoundary
  · exact selectedForest_of_repeatedOwners_mixed
      owner hInj small full q hSelectedCard hPrevious
      hSmallSub hSmallEdges hOverlap
      hSmallNonempty hSmallVertexCovered
      hFullEdgesAmbient hAmbientGirth
      selected hSelectedInj hSelectedContain
      tested hOld hSelectedTest hSmallEdgeTest

end StructuralRamsey.Girth
