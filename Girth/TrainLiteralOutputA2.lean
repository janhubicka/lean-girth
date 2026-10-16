import Girth.TrainLiteralOldPosHead
import Girth.TrainA2ContactTransfer
import Girth.TrainOldWagonNoInsertion
import Girth.TrainOutputWagonOrigin

/-!
# Circulation: output A2 for literal admissible replacement words

Only source acceptability, a strict PlanValid replacement, freshness,
and an actual literal output BigCycle are assumed.  Source A2 handles
inherited wagon contacts, while LongValid handles fresh ones. The
physical successor equations use the checked cyclic optional-word
transport.  This proves BOTH clauses of output A2 without assuming
output A2, A3, linearity or any appendix theorem.

The theorem does not construct the output BigCycle, prove A1/A3,
or establish arbitrary replacement-plan composition.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An inserted connector occurs directly BEFORE its retained old
right connector in the actual literal output BigCycle. -/
theorem BigCycle.literal_fresh_successor_oldPos
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInsertFresh : ∀ (r t : Fin n) (a : V ⊕ P),
      C.insertedConnector D pieces r = some a →
      a ≠ C.connector t)
    (hDifferent : ∀ (r t : Fin n) (a b : V ⊕ P),
      r ≠ t →
      C.insertedConnector D pieces r = some a →
      C.insertedConnector D pieces t = some b →
      a ≠ b)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n) (a : V ⊕ P)
    (ha : C.insertedConnector D pieces i = some a)
    (j : Fin m) (hj : B.connector j = a) :
    oldPos i = cyclicSucc j := by
  cases n with
  | zero =>
      have hn := C.length_ge_two
      omega
  | succ n' =>
      let w : List (V ⊕ P) :=
        optionalConnectorWord C.connector (C.insertedConnector D pieces)
      have hConnectors : List.ofFn B.connector = w := by
        calc
          List.ofFn B.connector =
              (List.ofFn (fun t : Fin m =>
                (B.label t, B.connector t))).map Prod.snd := by
                  simp [List.map_ofFn, Function.comp_def]
          _ = (C.resultWord D pieces).map Prod.snd :=
                congrArg (List.map Prod.snd) hWord
          _ = w := C.resultWord_connectorList D pieces
      have hLen : m = w.length := by
        have hh := congrArg List.length hConnectors
        simpa using hh
      have hAt (t : Fin m) :
          w.get (Fin.cast hLen t) = B.connector t := by
        have hPoint := congrArg
          (fun xs : List (V ⊕ P) => xs[t.val]?) hConnectors
        have htLt : t.val < (List.ofFn B.connector).length := by
          simpa using t.isLt
        have hLeft :
            (List.ofFn B.connector)[t.val]? =
              some (B.connector t) := by
          simpa [List.get_ofFn] using
            (List.getElem?_eq_getElem htLt)
        have hRight :
            w[t.val]? = some (w.get (Fin.cast hLen t)) :=
          List.getElem?_eq_getElem (Fin.cast hLen t).isLt
        exact Option.some.inj (hRight.symm.trans (hPoint.symm.trans hLeft))
      have hCastSucc (t : Fin m) :
          Fin.cast hLen (cyclicSucc t) =
            cyclicSucc (Fin.cast hLen t) := by
        apply Fin.ext
        change (t.val + 1) % m = (t.val + 1) % w.length
        exact congrArg (fun z : ℕ => (t.val + 1) % z) hLen
      have hFreshAt :
          w.get (Fin.cast hLen j) = a :=
        (hAt j).trans hj
      have hSuccessor :
          w.get (cyclicSucc (Fin.cast hLen j)) = C.connector i :=
        optionalConnectorWord_fresh_cyclic_successor
          C.connector (C.insertedConnector D pieces)
          hInsertFresh hDifferent i a ha
          (Fin.cast hLen j) hFreshAt
      have hActual :
          B.connector (cyclicSucc j) = C.connector i := by
        calc
          B.connector (cyclicSucc j) =
              w.get (Fin.cast hLen (cyclicSucc j)) := (hAt _).symm
          _ = w.get (cyclicSucc (Fin.cast hLen j)) := by
                rw [hCastSucc]
          _ = C.connector i := hSuccessor
      apply B.connector_injective
      exact (hConnector i).trans hActual.symm

/-- The actual literal output of a fresh strict PlanValid replacement
satisfies (A2), both for inherited and freshly inserted wagon connectors.
No output acceptability or output wagon linearity is assumed. -/
theorem BigCycle.output_A2_of_literal_resultWord
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hn : 3 ≤ n)
    (k : Fin n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hPlan : C.PlanValid D k pieces)
    (hFresh : ∀ (r : Fin n) (e : E) (p : P) (f : E),
      pieces r = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces) :
    B.A2 := by
  obtain ⟨oldPos, hConnector, hVertexPos⟩ :=
    C.oldPos_exists_of_literal_resultWord D B pieces hWord
  have hInsertFresh :
      ∀ (r t : Fin n) (a : V ⊕ P),
        C.insertedConnector D pieces r = some a →
        a ≠ C.connector t := by
    intro r t a ha
    cases hp : pieces r with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at ha
    | short e =>
        simp [BigCycle.insertedConnector, hp] at ha
    | long e p f =>
        have hap : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using ha.symm
        subst a
        exact (hFresh r e p f hp t).symm
  have hDifferent :
      ∀ (r t : Fin n) (a b : V ⊕ P),
        r ≠ t →
        C.insertedConnector D pieces r = some a →
        C.insertedConnector D pieces t = some b →
        a ≠ b := by
    intro r t a b hrt ha hb
    cases hp : pieces r with
    | keep =>
        simp [BigCycle.insertedConnector, hp] at ha
    | short e =>
        simp [BigCycle.insertedConnector, hp] at ha
    | long e p f =>
        have hap : a = (Sum.inr p : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using ha.symm
        cases hq : pieces t with
        | keep =>
            simp [BigCycle.insertedConnector, hq] at hb
        | short e =>
            simp [BigCycle.insertedConnector, hq] at hb
        | long g q h =>
            have hbq : b = (Sum.inr q : V ⊕ P) := by
              simpa [BigCycle.insertedConnector, hq] using hb.symm
            have hpq : p ≠ q :=
              C.plan_fresh_long_wagons_pairwise
                D hAccept hn k pieces hPlan hFresh
                r t hrt e f g h p q hp hq
            intro hab
            apply hpq
            exact Sum.inr.inj (hap.symm.trans (hab.trans hbq))
  apply C.A2_of_preserved_vertex_positions_and_wagons
    D B hAccept oldPos hConnector hVertexPos
  intro j p hj
  rcases C.output_wagon_old_or_long_of_literal_word
      D B pieces hWord oldPos hConnector j p hj with
    ⟨i, hji, hi⟩ | ⟨i, e, f, hPiece⟩
  · left
    have hNo := C.oldWagon_no_adjacent_insertions
      D k pieces hPlan i p hi
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
    have hLong : C.LongValid D k i e p f :=
      C.longValid_of_piece_eq_long D k i pieces hPlan e f p hPiece
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
    exact ⟨k, i, e, f, hLong,
      hFresh i e p f hPiece, hPrevPos, hHerePos⟩

end StructuralRamsey.Girth.OrderOneData
