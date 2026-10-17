import Girth.TrainSameConnectorSupremeTransfer
import Girth.TrainOptionalFreshCyclic
import Girth.TrainArbitraryGeometricA2
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: arbitrary literal replacement transfers A2 and acceptability

Unlike a strict supreme plan, arbitrary replacement may use edges
from different selected source labels. For source A2/A3 and an actual
literal output BigCycle, these labels do not matter.

Every output wagon connector is either old, with no possible insertion
adjacent to it, or comes from exactly one long source piece. Literal
connector injectivity gives pairwise uniqueness of fresh insertions;
the generic optional-block cyclic successor identifies every neighbour.
Each new long piece needs only LocalLongA2Geometry, not LongValid.

Thus the established label-independent output A2 interface closes
unconditionally once a genuine literal output is supplied. Together
with source linearity, arbitrary A3 and numerical twice-order transfer,
this proves the ACCEPTABILITY and NUMERICAL parts of the manuscript's
broad admissible-replacement lemma. The two other assertions,
automatic BigCycle legality for length >= 3 and composition of later
supreme copies, remain separate open problems.

No appendix theorem or output acceptability assumption is used.
-/

namespace StructuralRamsey.Girth

universe v
variable {α : Type v} {n : ℕ}

/-- The connector Nodup property of an optional insertion word
forces freshly inserted connectors at different source positions
to be distinct, whether or not freshness against OLD connectors
was separately assumed. -/
theorem optionalConnectorWord_insertions_different_of_nodup
    (base : Fin n → α) (insert : Fin n → Option α)
    (hNodup : (optionalConnectorWord base insert).Nodup) :
    ∀ (i j : Fin n) (a b : α),
      i ≠ j → insert i = some a → insert j = some b → a ≠ b := by
  classical
  have hFlatten :
      (List.ofFn (fun t : Fin n =>
        optionalConnectorBlock base insert t)).flatten.Nodup := by
    simpa only [optionalConnectorWord] using hNodup
  have hBetween := (List.nodup_flatten.mp hFlatten).2
  have hPairwise :
      ∀ ⦃i j : Fin n⦄, i < j →
        List.Disjoint (optionalConnectorBlock base insert i)
          (optionalConnectorBlock base insert j) :=
    List.pairwise_ofFn.mp hBetween
  intro i j a b hij hi hj hab
  have hAi : a ∈ optionalConnectorBlock base insert i := by
    simp [optionalConnectorBlock, hi]
  have hBj : b ∈ optionalConnectorBlock base insert j := by
    simp [optionalConnectorBlock, hj]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hd := hPairwise hlt
    exact ((List.disjoint_left.mp hd) hAi)
      (by simpa [hab] using hBj)
  · have hd := hPairwise hgt
    exact ((List.disjoint_left.mp hd) hBj)
      (by simpa [hab] using hAi)

namespace OrderOneData

variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- A source wagon connector forbids any fresh insertion immediately
before or after it, using just the original two vertex boundaries
of every long piece. No selected source target or PlanValid. -/
theorem BigCycle.oldWagon_no_adjacent_insertions_of_localGeometry
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongBoundaryGeometry D pieces)
    (i : Fin n) (p : P)
    (hOld : C.connector i = Sum.inr p) :
    C.insertedConnector D pieces i = none ∧
      C.insertedConnector D pieces (cyclicSucc i) = none := by
  constructor
  · cases hp : pieces i with
    | keep => simp [BigCycle.insertedConnector, hp]
    | short e => simp [BigCycle.insertedConnector, hp]
    | long e q f =>
        obtain ⟨x, y, _hPrev, hHere, _hQx, _hQy⟩ :=
          hGeom i e f q hp
        have hBad : (Sum.inr p : V ⊕ P) = Sum.inl y :=
          hOld.symm.trans hHere
        cases hBad
  · cases hp : pieces (cyclicSucc i) with
    | keep => simp [BigCycle.insertedConnector, hp]
    | short e => simp [BigCycle.insertedConnector, hp]
    | long e q f =>
        obtain ⟨x, y, hPrev, _hHere, _hQx, _hQy⟩ :=
          hGeom (cyclicSucc i) e f q hp
        rw [trainCyclicPred_cyclicSucc_of_two_le C.length_ge_two i]
          at hPrev
        have hBad : (Sum.inr p : V ⊕ P) = Sum.inl x :=
          hOld.symm.trans hPrev
        cases hBad

/-- Actual output connector injectivity makes all NEW insertions
pairwise distinct. This is valid even for arbitrary replacement
pieces with no uniform selected supreme label. -/
theorem BigCycle.literal_output_inserts_different
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces) :
    ∀ (i j : Fin n) (a b : V ⊕ P),
      i ≠ j →
      C.insertedConnector D pieces i = some a →
      C.insertedConnector D pieces j = some b →
      a ≠ b := by
  have hB : (List.ofFn B.connector).Nodup := by
    rw [List.nodup_iff_injective_get]
    intro i j h
    apply Fin.ext
    have heq :
        (Fin.cast (by simp) i : Fin m) =
        (Fin.cast (by simp) j : Fin m) :=
      B.connector_injective (by simpa only [List.get_ofFn] using h)
    simpa using congrArg Fin.val heq
  have hConnectorWord :
      List.ofFn B.connector =
        optionalConnectorWord C.connector
          (C.insertedConnector D pieces) := by
    calc
      List.ofFn B.connector =
          (List.ofFn (fun t : Fin m =>
            (B.label t, B.connector t))).map Prod.snd := by
              simp [List.map_ofFn, Function.comp_def]
      _ = (C.resultWord D pieces).map Prod.snd :=
            congrArg (List.map Prod.snd) hWord
      _ = optionalConnectorWord C.connector
            (C.insertedConnector D pieces) :=
              C.resultWord_connectorList D pieces
  have hNodup :
      (optionalConnectorWord C.connector
        (C.insertedConnector D pieces)).Nodup := by
    rw [← hConnectorWord]
    exact hB
  exact optionalConnectorWord_insertions_different_of_nodup
    C.connector (C.insertedConnector D pieces) hNodup

/-- Fully instantiate the abstract geometric output A2 transfer
for the ACTUAL literal word of an arbitrary locally geometric
replacement. No PlanValid and no output A2 premise are needed. -/
theorem BigCycle.output_A2_of_arbitrary_literal_geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    B.A2 := by
  obtain ⟨oldPos, hConnector, hVertexPos⟩ :=
    C.oldPos_exists_of_literal_resultWord D B pieces hWord
  have hBoundary : C.LocalLongBoundaryGeometry D pieces :=
    C.localLongBoundaryGeometry_of_A2 D pieces hGeom
  have hInsertFresh :
      ∀ (i t : Fin n) (a : V ⊕ P),
        C.insertedConnector D pieces i = some a →
        a ≠ C.connector t := by
    intro i t a ha
    cases hp : pieces i with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at ha
    | short e =>
        simp [BigCycle.insertedConnector, hp] at ha
    | long e p f =>
        have hAP : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using ha.symm
        subst a
        exact (hFresh i e p f hp t).symm
  have hDifferent :=
    C.literal_output_inserts_different D B pieces hWord
  apply C.A2_of_preserved_vertices_and_geometric_wagons
    D B hAccept.2.1 hAccept.2.2 oldPos hConnector hVertexPos
  intro j p hj
  rcases C.output_wagon_old_or_long_of_literal_word
      D B pieces hWord oldPos hConnector j p hj with
    ⟨i, hji, hi⟩ | ⟨i, e, f, hPiece⟩
  · left
    have hNo :=
      C.oldWagon_no_adjacent_insertions_of_localGeometry
        D pieces hBoundary i p hi
    have hNoPrev :
        C.insertedConnector D pieces
          (cyclicSucc (trainCyclicPred i)) = none := by
      simpa [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i]
        using hNo.1
    have hBefore := C.literal_oldPos_successor_of_noInsertion
      D B pieces hFresh hWord oldPos hConnector
      (trainCyclicPred i) hNoPrev
    have hAfter := C.literal_oldPos_successor_of_noInsertion
      D B pieces hFresh hWord oldPos hConnector i hNo.2
    have hBeforeEq :
        oldPos i = cyclicSucc (oldPos (trainCyclicPred i)) := by
      simpa [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i]
        using hBefore
    have hPredPos :
        oldPos (trainCyclicPred i) = trainCyclicPred j := by
      calc
        oldPos (trainCyclicPred i) =
            trainCyclicPred (cyclicSucc (oldPos (trainCyclicPred i))) :=
              (trainCyclicPred_cyclicSucc_of_two_le
                B.length_ge_two (oldPos (trainCyclicPred i))).symm
        _ = trainCyclicPred (oldPos i) :=
              congrArg trainCyclicPred hBeforeEq.symm
        _ = trainCyclicPred j := by rw [hji]
    have hSuccPos : oldPos (cyclicSucc i) = cyclicSucc j := by
      simpa [hji] using hAfter
    exact ⟨i, hji, hi, hPredPos, hSuccPos⟩
  · right
    obtain ⟨x, y, hCx, hCy, hWx, hWy, hNonedge⟩ :=
      hGeom i e f p hPiece
    have hNew : C.insertedConnector D pieces i = some (Sum.inr p) := by
      simp [BigCycle.insertedConnector, hPiece]
    have hNewPrev :
        C.insertedConnector D pieces
          (cyclicSucc (trainCyclicPred i)) = some (Sum.inr p) := by
      simpa [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i]
        using hNew
    have hPreFresh :
        B.connector (cyclicSucc (oldPos (trainCyclicPred i))) =
          Sum.inr p :=
      C.literal_oldPos_successor_inserted
        D B pieces hFresh hWord oldPos hConnector
        (trainCyclicPred i) (Sum.inr p) hNewPrev
    have hOutputIndex :
        cyclicSucc (oldPos (trainCyclicPred i)) = j :=
      B.connector_injective (hPreFresh.trans hj.symm)
    have hPrevPos :
        oldPos (trainCyclicPred i) = trainCyclicPred j := by
      calc
        oldPos (trainCyclicPred i) =
            trainCyclicPred (cyclicSucc (oldPos (trainCyclicPred i))) :=
              (trainCyclicPred_cyclicSucc_of_two_le
                B.length_ge_two (oldPos (trainCyclicPred i))).symm
        _ = trainCyclicPred j := congrArg trainCyclicPred hOutputIndex
    have hHerePos : oldPos i = cyclicSucc j :=
      C.literal_fresh_successor_oldPos
        D B pieces hInsertFresh hDifferent
        hWord oldPos hConnector i (Sum.inr p) hNew j hj
    exact ⟨i, x, y, hCx, hCy, hWx, hWy,
      hFresh i e p f hPiece, hNonedge, hPrevPos, hHerePos⟩

/-- A2, A3 and numerical twice-order are all preserved by an
arbitrary fresh locally geometric replacement whose literal
expanded word is a genuine BigCycle. Source wagon linearity is
used only for A3, not for A2 or the numerical equality. -/
theorem BigCycle.output_A2_A3_order_of_arbitrary_geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces) :
    B.A2 ∧ B.A3 ∧ B.twiceOrder = C.twiceOrder := by
  exact ⟨C.output_A2_of_arbitrary_literal_geometry
      D B hAccept pieces hGeom hFresh hWord,
    C.output_A3_of_arbitrary_A2Geometry
      D B hAccept.2.2 hLinear pieces hGeom hFresh hWord,
    C.literal_resultWord_twiceOrder_of_arbitrary_A2Geometry
      D B pieces hGeom hWord⟩

/-- The ACCEPTABILITY and numerical-order assertions of the
circulation's general admissible-replacement lemma, conditional on
the output being a legal BigCycle and on retention of a designated
occurrence when the source has order one.
Supreme-copy composition and automatic big-cycle legality remain open. -/
theorem BigCycle.output_acceptable_order_of_arbitrary_geometry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (pieces : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (hRetain : C.twiceOrder = 2 →
      ∃ j : Fin m, D.designated (B.label j)) :
    B.Acceptable ∧ B.twiceOrder = C.twiceOrder := by
  obtain ⟨hA2, hA3, hOrder⟩ :=
    C.output_A2_A3_order_of_arbitrary_geometry
      D B hAccept hLinear pieces hGeom hFresh hWord
  refine ⟨⟨?_, hA2, hA3⟩, hOrder⟩
  intro hOutOrder
  exact hRetain (hOrder.symm.trans hOutOrder)

end OrderOneData
end StructuralRamsey.Girth
