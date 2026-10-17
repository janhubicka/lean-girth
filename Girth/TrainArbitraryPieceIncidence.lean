import Girth.TrainArbitraryConnectorNodup
import Girth.TrainExpandedWordChain

/-!
# Circulation: physical incidence checks for arbitrary replacement pieces

A locally chosen short edge needs incidence with both original source
connectors. A long piece needs distinct physical edges in its inserted
wagon, with the first edge meeting its original left connector and the
last meeting its right connector. Keeping a source occurrence needs
no extra check.

No source labels of NEW edges are required to lie in one designated
copy. This local condition proves every internal replacement-block
chain and both physical boundary incidence statements, leaving only
the different-label boundary test for automatic BigCycle legality.

The selected-label PlanValid hypothesis is not used; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Exactly the local physical incidence needed for a word of kept,
short, and long replacement blocks, without a common supreme target. -/
def BigCycle.LocalPieceIncidence
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P) : Prop :=
  ∀ i : Fin n,
    match pieces i with
    | .keep => True
    | .short e =>
        D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
        D.Incident (.inr e) (C.connector i)
    | .long e p f =>
        e ≠ f ∧
        D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
        D.parent e = p ∧ D.parent f = p ∧
        D.Incident (.inr f) (C.connector i)

/-- Each physical replacement block is internally a chain.
Only a genuine long block contains an internal adjacent pair. -/
theorem BigCycle.pieceWord_isChain_of_localIncidence
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hLocal : C.LocalPieceIncidence D pieces)
    (i : Fin n) :
    (C.pieceWord D i (pieces i)).IsChain D.CyclicPairFollow := by
  cases hp : pieces i with
  | keep =>
      simp [BigCycle.pieceWord]
  | short e =>
      simp [BigCycle.pieceWord]
  | long e p f =>
      have hv : e ≠ f ∧
          D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
          D.parent e = p ∧ D.parent f = p ∧
          D.Incident (.inr f) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hLocal i
      change ([(Sum.inr e, Sum.inr p),
        (Sum.inr f, C.connector i)]).IsChain D.CyclicPairFollow
      apply List.isChain_pair.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        exact hv.1 (Sum.inr.inj heq)
      · exact ⟨e, rfl, hv.2.2.1⟩
      · exact ⟨f, rfl, hv.2.2.2.1⟩

/-- The last label of each block meets the original RIGHT connector.
No chosen supreme label is needed. -/
theorem BigCycle.pieceLast_incident_of_localIncidence
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hLocal : C.LocalPieceIncidence D pieces)
    (i : Fin n) :
    D.Incident (C.pieceLastLabel D (C.label i) (pieces i))
      (C.connector i) := by
  cases hp : pieces i with
  | keep =>
      simpa [BigCycle.pieceLastLabel, hp] using C.left_incident i
  | short e =>
      have hv : D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
          D.Incident (.inr e) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hLocal i
      simpa [BigCycle.pieceLastLabel, hp] using hv.2
  | long e p f =>
      have hv : e ≠ f ∧
          D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
          D.parent e = p ∧ D.parent f = p ∧
          D.Incident (.inr f) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hLocal i
      simpa [BigCycle.pieceLastLabel, hp] using hv.2.2.2.2

/-- The first label of each block meets the old LEFT connector. -/
theorem BigCycle.pieceFirst_incident_of_localIncidence
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (hLocal : C.LocalPieceIncidence D pieces)
    (i : Fin n) :
    D.Incident (C.pieceFirstLabel D (C.label i) (pieces i))
      (C.connector (trainCyclicPred i)) := by
  cases hp : pieces i with
  | keep =>
      have hh := C.right_incident (trainCyclicPred i)
      rw [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i] at hh
      simpa [BigCycle.pieceFirstLabel, hp] using hh
  | short e =>
      have hv : D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
          D.Incident (.inr e) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hLocal i
      simpa [BigCycle.pieceFirstLabel, hp] using hv.1
  | long e p f =>
      have hv : e ≠ f ∧
          D.Incident (.inr e) (C.connector (trainCyclicPred i)) ∧
          D.parent e = p ∧ D.parent f = p ∧
          D.Incident (.inr f) (C.connector i) := by
        simpa [BigCycle.LocalPieceIncidence, hp] using hLocal i
      simpa [BigCycle.pieceFirstLabel, hp] using hv.2.1

end StructuralRamsey.Girth.OrderOneData
