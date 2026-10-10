import Girth.ForestDirectIncrementConditional
import Girth.ForestMixedOneEdgeOwners
import Girth.ForestOneEdgeOwnerLocalTest

/-!
# Apply the complete conditional forest increment to mixed owners

A selected core edge which is not known to belong to a designated
local gluing copy owns itself.  Regular local gluing copies have their
full standard-picture extensions as outer owners, while exceptional
edges remain one-edge pieces on both sides.

The previous-cutoff local forest bound is imposed on this actual MIXED
family of local gluing pieces and one-edge members.  The old-picture
q-forest bound is imposed only at regular owners: the exceptional
one-edge owner has the trivial finite-mixed-forest property.

The only boundary hypothesis for exceptional owners is that their
chosen core edge belongs to the local support K and lies in the core.
The exact small-or-whole boundary condition is proved below, not
assumed for exceptional owners.

This is an abstract hypergraph/interface theorem.  The concrete
relational partite attachment, finite selected-family extraction and
the recursive train Ramsey theorem are separate proof obligations.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q E N : Type v}

/-- A selected whole core edge has the precise boundary required by
the all-distinct-owner argument. -/
theorem oneEdge_smallOrWholeBoundary
    (K : Set (Set W)) (S e : Set W)
    (hK : e ∈ K) (hS : e ⊆ S) :
    SmallOrWholeEdgeBoundary K S (HypergraphPiece.oneEdge e) := by
  right
  refine ⟨e, hK, ?_, ?_⟩
  · simp [HypergraphPiece.oneEdge]
  · exact Set.inter_eq_left.mpr hS

/-- The actual mixed-owner direct increment, without a redundant
edge-coverage premise on the recursively constructed local witness.

Only designated standard-picture owners need the old-picture mixed
q-forest hypothesis.  Uncovered selected local edges are represented
by one-edge owners, for which that hypothesis is automatic. -/
theorem selectedForest_of_mixedOwnerDirectIncrement
    [Fintype N] [Nonempty N]
    (owner : N → Q ⊕ E)
    (small full : Q → HypergraphPiece W)
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
    (hSmallInCore :
      ∀ i : Q, (small i).carrier ⊆ S)
    (K : Set (Set W))
    (hCoreEdgeLocal : ∀ e : E, coreEdge e ∈ K)
    (hCoreEdgeSub : ∀ e : E, coreEdge e ⊆ S)
    (hGirth : GirthGT K q)
    (hRegularBoundary :
      ∀ (n : N) (i : Q), owner n = Sum.inl i →
        SmallOrWholeEdgeBoundary K S (selected n))
    (hExceptionalSelected :
      ∀ (n : N) (e : E), owner n = Sum.inr e →
        selected n = HypergraphPiece.oneEdge (coreEdge e))
    {Ambient : Set (Set W)}
    (hRegularAmbient :
      ∀ i : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full i).edges → e ∈ Ambient)
    (hCoreAmbient : ∀ i : E, coreEdge i ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (hSelectedContain :
      ∀ n, (selected n).carrier ⊆
        (mixedOwnerFull full coreEdge (owner n)).carrier)
    (tested : Q → HypergraphPiece W → Prop)
    (hOld : ∀ i : Q, FiniteMixedForestThrough (tested i) q)
    (hRegularSelectedTest :
      ∀ (n : N) (i : Q), owner n = Sum.inl i →
        tested i (selected n))
    (hRegularEdgeTest :
      ∀ (i : Q) (e : Set W), e ∈ (small i).edges →
        tested i (HypergraphPiece.oneEdge e)) :
    ForestOfCopies selected := by
  classical
  let testedMixed : Q ⊕ E → HypergraphPiece W → Prop :=
    fun i P => match i with
      | .inl a => tested a P
      | .inr b => P = HypergraphPiece.oneEdge (coreEdge b)
  have hOldMixed :
      ∀ i : Q ⊕ E, FiniteMixedForestThrough (testedMixed i) q := by
    intro i
    cases i with
    | inl a => exact hOld a
    | inr b => exact finiteMixedForestThrough_singleEdge (coreEdge b) q
  have hSelectedTestMixed :
      ∀ n : N, testedMixed (owner n) (selected n) := by
    intro n
    cases h : owner n with
    | inl a =>
        change tested a (selected n)
        exact hRegularSelectedTest n a h
    | inr b =>
        change selected n = HypergraphPiece.oneEdge (coreEdge b)
        exact hExceptionalSelected n b h
  have hSmallEdgeTestMixed :
      ∀ i : Q ⊕ E, ∀ (e : Set W),
        e ∈ (mixedOwnerSmall small coreEdge i).edges →
        testedMixed i (HypergraphPiece.oneEdge e) := by
    intro i e he
    cases i with
    | inl a =>
        change tested a (HypergraphPiece.oneEdge e)
        exact hRegularEdgeTest a e he
    | inr b =>
        have hEq : e = coreEdge b := by
          simpa [mixedOwnerSmall, HypergraphPiece.oneEdge] using he
        change HypergraphPiece.oneEdge e =
          HypergraphPiece.oneEdge (coreEdge b)
        rw [hEq]
  have hSmallNonemptyMixed :
      ∀ i : Q ⊕ E,
        (mixedOwnerSmall small coreEdge i).edges.Nonempty := by
    intro i
    cases i with
    | inl a => exact hSmallNonempty a
    | inr b =>
        refine ⟨coreEdge b, ?_⟩
        simp [mixedOwnerSmall, HypergraphPiece.oneEdge]
  have hSmallCoveredMixed :
      ∀ i : Q ⊕ E, ∀ x : W,
        x ∈ (mixedOwnerSmall small coreEdge i).carrier →
          ∃ e : Set W,
            e ∈ (mixedOwnerSmall small coreEdge i).edges ∧ x ∈ e := by
    intro i x hx
    cases i with
    | inl a => exact hSmallCovered a x hx
    | inr b =>
        refine ⟨coreEdge b, ?_, ?_⟩
        · simp [mixedOwnerSmall, HypergraphPiece.oneEdge]
        · exact hx
  have hSmallInCoreMixed :
      ∀ i : Q ⊕ E,
        (mixedOwnerSmall small coreEdge i).carrier ⊆ S := by
    intro i
    cases i with
    | inl a => exact hSmallInCore a
    | inr b => exact hCoreEdgeSub b
  have hBoundaryMixed :
      ∀ n, SmallOrWholeEdgeBoundary K S (selected n) := by
    intro n
    cases h : owner n with
    | inl a => exact hRegularBoundary n a h
    | inr b =>
        rw [hExceptionalSelected n b h]
        exact oneEdge_smallOrWholeBoundary K S (coreEdge b)
          (hCoreEdgeLocal b) (hCoreEdgeSub b)
  have hFullAmbientMixed :
      ∀ i : Q ⊕ E, ∀ ⦃e : Set W⦄,
        e ∈ (mixedOwnerFull full coreEdge i).edges → e ∈ Ambient := by
    intro i e he
    cases i with
    | inl a => exact hRegularAmbient a he
    | inr b =>
        have hEq : e = coreEdge b := by
          simpa [mixedOwnerFull, HypergraphPiece.oneEdge] using he
        rw [hEq]
        exact hCoreAmbient b
  exact selectedForest_of_directPictureIncrement
    owner (mixedOwnerSmall small coreEdge)
    (mixedOwnerFull full coreEdge)
    selected hSelectedInj q hq hCount hPrevious
    (mixedOwner_carrier_subset small full coreEdge hRegularSub)
    (mixedOwner_edges_subset small full coreEdge hRegularEdges)
    (mixedOwner_pair_overlap small full S coreEdge
      hRegularSub hRegularOverlap hFullCore hCoreEdgeSub)
    hSmallNonemptyMixed hSmallCoveredMixed
    S hSmallInCoreMixed K hGirth hBoundaryMixed
    hFullAmbientMixed hAmbientGirth
    hSelectedContain testedMixed hOldMixed
    hSelectedTestMixed hSmallEdgeTestMixed

end StructuralRamsey.Girth
