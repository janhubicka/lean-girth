import Girth.ForestMixedDirectIncrement

/-!
# Choosing the mixed outer owner of each selected picture-step piece

The picture-step argument selects a finite set of genuine A-support
pieces and designated B-support pieces. Each chosen piece is either:
* a regular selected piece in one full standard picture, with an old
  tested preimage and the exact small-or-whole local core boundary; or
* a selected ambient core A-edge, which can own itself even if no
  local designated picture contains it.

The owner function is a finite choice from these actual cases. This
removes any need to postulate an owner map as a separate hypothesis
in a concrete application. The geometric case distinction and
previous-cutoff mixed forest invariant remain explicit hypotheses.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q E N : Type v}

/-- A concrete selected piece has a regular standard-picture owner
with tested old support and exact boundary, or is itself a core edge. -/
def MixedOwnerSelectionCertificate
    (selected : HypergraphPiece W)
    (full : Q → HypergraphPiece W)
    (coreEdge : E → Set W)
    (S : Set W) (K : Set (Set W))
    (tested : Q → HypergraphPiece W → Prop) :
    Q ⊕ E → Prop
  | .inl i =>
      selected.carrier ⊆ (full i).carrier ∧
      tested i selected ∧
      SmallOrWholeEdgeBoundary K S selected
  | .inr e =>
      selected = HypergraphPiece.oneEdge (coreEdge e)

/-- A verified case distinction produces the mixed owner map and
all three per-selected-member obligations needed by the conditional
direct forest increment.  In particular the uncovered core-edge
case is exactly a one-edge owner, not an auxiliary fictitious B-copy. -/
theorem mixedOwnerChoice_exists
    (full : Q → HypergraphPiece W)
    (coreEdge : E → Set W)
    (S : Set W) (K : Set (Set W))
    (tested : Q → HypergraphPiece W → Prop)
    (selected : N → HypergraphPiece W)
    (hCases : ∀ n : N,
      ∃ o : Q ⊕ E,
        MixedOwnerSelectionCertificate
          (selected n) full coreEdge S K tested o) :
    ∃ owner : N → Q ⊕ E,
      (∀ n, (selected n).carrier ⊆
        (mixedOwnerFull full coreEdge (owner n)).carrier) ∧
      (∀ (n : N) (i : Q), owner n = Sum.inl i →
        SmallOrWholeEdgeBoundary K S (selected n)) ∧
      (∀ (n : N) (e : E), owner n = Sum.inr e →
        selected n = HypergraphPiece.oneEdge (coreEdge e)) ∧
      (∀ (n : N) (i : Q), owner n = Sum.inl i →
        tested i (selected n)) := by
  classical
  let owner : N → Q ⊕ E := fun n =>
    Classical.choose (hCases n)
  have hCert (n : N) :
      MixedOwnerSelectionCertificate
        (selected n) full coreEdge S K tested (owner n) :=
    Classical.choose_spec (hCases n)
  refine ⟨owner, ?_, ?_, ?_, ?_⟩
  · intro n
    have hh := hCert n
    cases h : owner n with
    | inl i =>
        rw [h] at hh
        change (selected n).carrier ⊆ (full i).carrier ∧
          tested i (selected n) ∧
          SmallOrWholeEdgeBoundary K S (selected n) at hh
        simpa only [h, mixedOwnerFull] using hh.1
    | inr e =>
        rw [h] at hh
        change selected n = HypergraphPiece.oneEdge (coreEdge e) at hh
        rw [hh]
        exact Set.Subset.rfl
  · intro n i hi
    have hh := hCert n
    rw [hi] at hh
    exact hh.2.2
  · intro n e he
    have hh := hCert n
    rw [he] at hh
    exact hh
  · intro n i hi
    have hh := hCert n
    rw [hi] at hh
    exact hh.2.1

/-- A full selected-family forest follows from the regular/exceptional
case distinction without separately choosing a covering designated
copy for an uncovered local edge. -/
theorem selectedForest_of_mixedOwnerClassification
    [Fintype N] [Nonempty N]
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
    {Ambient : Set (Set W)}
    (hRegularAmbient :
      ∀ i : Q, ∀ ⦃e : Set W⦄,
        e ∈ (full i).edges → e ∈ Ambient)
    (hCoreAmbient : ∀ i : E, coreEdge i ∈ Ambient)
    (hAmbientGirth : GirthGT Ambient 2)
    (tested : Q → HypergraphPiece W → Prop)
    (hOld : ∀ i : Q, FiniteMixedForestThrough (tested i) q)
    (hRegularEdgeTest :
      ∀ (i : Q) (e : Set W), e ∈ (small i).edges →
        tested i (HypergraphPiece.oneEdge e))
    (hCases : ∀ n : N,
      ∃ o : Q ⊕ E,
        MixedOwnerSelectionCertificate
          (selected n) full coreEdge S K tested o) :
    ForestOfCopies selected := by
  obtain ⟨owner, hContain, hBoundary, hExceptional, hSelectedTest⟩ :=
    mixedOwnerChoice_exists
      full coreEdge S K tested selected hCases
  exact selectedForest_of_mixedOwnerDirectIncrement
    owner small full S coreEdge selected hSelectedInj
    q hq hCount hPrevious
    hRegularSub hRegularEdges hRegularOverlap hFullCore
    hSmallNonempty hSmallCovered hSmallInCore
    K hCoreEdgeLocal hCoreEdgeSub hGirth
    hBoundary hExceptional hRegularAmbient hCoreAmbient
    hAmbientGirth hContain tested hOld
    hSelectedTest hRegularEdgeTest

end StructuralRamsey.Girth
