import Girth.TrainFreshWagonA2

/-!
# Circulation: transfer A2 across genuine long-wagon insertions

The checked word assembly already gives an actual output BigCycle.
A2 is a separate property: old wagon connectors retain their two
adjacent original positions, while each NEW wagon connector comes from
a locally valid fresh long piece.

An inserted long piece has exactly its two old source boundary contacts,
and its boundary vertices have no common physical ambient edge. Those
facts are already checked in TrainFreshWagonA2.

This module proves A2 for the ACTUAL output BigCycle from the old
acceptable cycle, provided the following concrete bookkeeping data:
  * oldPos records every retained old connector in the output;
  * every OUTPUT vertex-wagon contact pulls back to a source contact;
  * every output wagon connector is either an old wagon with unchanged
    predecessor/successor positions, or a fresh LongValid wagon inserted
    between its two source vertex boundary positions.

The conclusion B.A2 is NOT a premise. No output wagon linearity,
B.Acceptable, A3-transfer, supra-cycle collapse, or appendix lemma
is assumed. The next task is constructing these bookkeeping facts for
the literal resultWord of a PlanValid fresh replacement.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The actual source-side reason a wagon connector appears in the
replacement output: either it was retained from the old cycle with
its adjacent connector positions unchanged, or it is an inserted
fresh wagon backed by two physical edges of a LongValid piece. -/
def BigCycle.OutputWagonCase
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (oldPos : Fin n → Fin m) (j : Fin m) (p : P) : Prop :=
  (∃ i : Fin n,
    j = oldPos i ∧
    C.connector i = Sum.inr p ∧
    oldPos (trainCyclicPred i) = trainCyclicPred j ∧
    oldPos (cyclicSucc i) = cyclicSucc j)
  ∨
  (∃ (k i : Fin n) (e f : E),
    C.LongValid D k i e p f ∧
    (∀ t : Fin n, C.connector t ≠ Sum.inr p) ∧
    oldPos (trainCyclicPred i) = trainCyclicPred j ∧
    oldPos i = cyclicSucc j)

/-- Given genuine old connector positions, contact pullback and real
long-piece witnesses, the source A2 condition transfers to the
output BigCycle. This proves BOTH the location and the no-ambient-edge
parts of A2, including the fresh inserted wagon cases. -/
theorem BigCycle.A2_of_inherited_and_fresh_long
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hContactPullback : ∀ (p : P) (j : Fin m),
      B.InWagonAt p j →
      ∃ i : Fin n, j = oldPos i ∧ C.InWagonAt p i)
    (hWagonCase : ∀ (j : Fin m) (p : P),
      B.connector j = Sum.inr p →
      C.OutputWagonCase D B oldPos j p) :
    B.A2 := by
  constructor
  · intro j p hj t ht
    obtain ⟨u, htu, hu⟩ := hContactPullback p t ht
    rcases hWagonCase j p hj with hOld | hNew
    · obtain ⟨i, hji, hi, hPrev, hSucc⟩ := hOld
      rcases hAccept.2.1.1 i p hi u hu with hBefore | hAfter
      · left
        calc
          t = oldPos u := htu
          _ = oldPos (trainCyclicPred i) := congrArg oldPos hBefore
          _ = trainCyclicPred j := hPrev
      · right
        calc
          t = oldPos u := htu
          _ = oldPos (cyclicSucc i) := congrArg oldPos hAfter
          _ = cyclicSucc j := hSucc
    · obtain ⟨k, i, e, f, hLong, hFresh, hPrev, hHere⟩ := hNew
      have hContact := C.fresh_wagon_contacts_of_longValid
        D hAccept k i e f p hLong hFresh u hu
      rcases hContact with hBefore | hAfter
      · left
        calc
          t = oldPos u := htu
          _ = oldPos (trainCyclicPred i) := congrArg oldPos hBefore
          _ = trainCyclicPred j := hPrev
      · right
        calc
          t = oldPos u := htu
          _ = oldPos i := congrArg oldPos hAfter
          _ = cyclicSucc j := hHere
  · intro j p x y hj hPrev hSucc hDifferent hPx hPy
    rcases hWagonCase j p hj with hOld | hNew
    · obtain ⟨i, hji, hi, hPredPos, hSuccPos⟩ := hOld
      have hOldPrev : C.connector (trainCyclicPred i) = Sum.inl x := by
        calc
          C.connector (trainCyclicPred i) =
              B.connector (oldPos (trainCyclicPred i)) :=
                (hConnector _).symm
          _ = B.connector (trainCyclicPred j) :=
              congrArg B.connector hPredPos
          _ = Sum.inl x := hPrev
      have hOldSucc : C.connector (cyclicSucc i) = Sum.inl y := by
        calc
          C.connector (cyclicSucc i) =
              B.connector (oldPos (cyclicSucc i)) :=
                (hConnector _).symm
          _ = B.connector (cyclicSucc j) :=
              congrArg B.connector hSuccPos
          _ = Sum.inl y := hSucc
      have hOldDifferent :
          trainCyclicPred i ≠ cyclicSucc i := by
        intro heq
        apply hDifferent
        calc
          trainCyclicPred j = oldPos (trainCyclicPred i) := hPredPos.symm
          _ = oldPos (cyclicSucc i) := congrArg oldPos heq
          _ = cyclicSucc j := hSuccPos
      exact hAccept.2.1.2 i p x y hi hOldPrev hOldSucc
        hOldDifferent hPx hPy
    · obtain ⟨k, i, e, f, hLong, _hFresh, hPredPos, hHerePos⟩ := hNew
      obtain ⟨x₀, y₀, hCPrev, hCHere, _he, _hf, _hDistinct,
        _hep, _hfp, _hxe, _hyf, hNoPair⟩ := hLong
      have hBx : B.connector (trainCyclicPred j) = Sum.inl x₀ := by
        calc
          B.connector (trainCyclicPred j) =
              B.connector (oldPos (trainCyclicPred i)) :=
                congrArg B.connector hPredPos.symm
          _ = C.connector (trainCyclicPred i) := hConnector _
          _ = Sum.inl x₀ := hCPrev
      have hBy : B.connector (cyclicSucc j) = Sum.inl y₀ := by
        calc
          B.connector (cyclicSucc j) = B.connector (oldPos i) :=
            congrArg B.connector hHerePos.symm
          _ = C.connector i := hConnector i
          _ = Sum.inl y₀ := hCHere
      have hxx : x = x₀ := Sum.inl.inj (hPrev.symm.trans hBx)
      have hyy : y = y₀ := Sum.inl.inj (hSucc.symm.trans hBy)
      rw [hxx, hyy]
      exact hNoPair


/-- No NEW vertex connectors is the only additional information needed
to pull output wagon-vertex contacts back to their old source positions.
Wagon membership itself is unchanged because source and output use
the very same physical OrderOneData. -/
theorem BigCycle.wagon_contacts_pullback_of_vertex_positions
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hVertexPos : ∀ (j : Fin m) (x : V),
      B.connector j = Sum.inl x →
      ∃ i : Fin n, j = oldPos i) :
    ∀ (p : P) (j : Fin m), B.InWagonAt p j →
      ∃ i : Fin n, j = oldPos i ∧ C.InWagonAt p i := by
  intro p j hj
  obtain ⟨x, hBx, hPx⟩ := hj
  obtain ⟨i, hPos⟩ := hVertexPos j x hBx
  refine ⟨i, hPos, x, ?_, hPx⟩
  calc
    C.connector i = B.connector (oldPos i) := (hConnector i).symm
    _ = B.connector j := congrArg B.connector hPos.symm
    _ = Sum.inl x := hBx

/-- Consequently the full source-to-output A2 transfer requires only
the old connector-position map, the fact that every output VERTEX
position is inherited, and the source origin of wagon connectors.
No separate opaque contact-pullback assumption is necessary. -/
theorem BigCycle.A2_of_preserved_vertex_positions_and_wagons
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (hVertexPos : ∀ (j : Fin m) (x : V),
      B.connector j = Sum.inl x →
      ∃ i : Fin n, j = oldPos i)
    (hWagonCase : ∀ (j : Fin m) (p : P),
      B.connector j = Sum.inr p →
      C.OutputWagonCase D B oldPos j p) :
    B.A2 := by
  apply C.A2_of_inherited_and_fresh_long D B hAccept oldPos
    hConnector
  · exact C.wagon_contacts_pullback_of_vertex_positions D B
      oldPos hConnector hVertexPos
  · exact hWagonCase

end StructuralRamsey.Girth.OrderOneData
