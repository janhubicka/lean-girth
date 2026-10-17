import Girth.TrainArbitraryLiteralA2

/-!
# Circulation: physical neighbours of a first-stage long insertion

The existing arbitrary-output A2 proof already establishes these
indices internally. Export the exact equations for later composition:
a long block inserts its wagon immediately after the inherited
previous connector and immediately before its own old connector.

No designated target, first PlanValid, later supreme plan, appendix
theorem, or output acceptability is assumed.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The source boundaries of a long replacement are the precise two
neighbours of its fresh wagon in the actual literal output. -/
theorem BigCycle.literal_long_fresh_neighbours
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (first : Fin n → TrainSupremePiece E P)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      first i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D first)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n) (e f : E) (p : P)
    (hPiece : first i = .long e p f)
    (j : Fin m) (hj : B.connector j = Sum.inr p) :
    oldPos (trainCyclicPred i) = trainCyclicPred j ∧
      oldPos i = cyclicSucc j := by
  have hNew : C.insertedConnector D first i = some (Sum.inr p) := by
    simp [BigCycle.insertedConnector, hPiece]
  have hNewPred : C.insertedConnector D first
      (cyclicSucc (trainCyclicPred i)) = some (Sum.inr p) := by
    simpa [cyclicSucc_trainCyclicPred_of_two_le C.length_ge_two i]
      using hNew
  have hBNew : B.connector
      (cyclicSucc (oldPos (trainCyclicPred i))) = Sum.inr p :=
    C.literal_oldPos_successor_inserted
      D B first hFresh hWord oldPos hConnector
      (trainCyclicPred i) (Sum.inr p) hNewPred
  have hPosition :
      cyclicSucc (oldPos (trainCyclicPred i)) = j :=
    B.connector_injective (hBNew.trans hj.symm)
  have hLeft : oldPos (trainCyclicPred i) = trainCyclicPred j := by
    calc
      oldPos (trainCyclicPred i) =
          trainCyclicPred (cyclicSucc (oldPos (trainCyclicPred i))) :=
            (trainCyclicPred_cyclicSucc_of_two_le
              B.length_ge_two (oldPos (trainCyclicPred i))).symm
      _ = trainCyclicPred j := congrArg trainCyclicPred hPosition
  have hInsertFresh :
      ∀ (r t : Fin n) (a : V ⊕ P),
        C.insertedConnector D first r = some a →
        a ≠ C.connector t := by
    intro r t a ha
    cases hp : first r with
    | keep => simp [BigCycle.insertedConnector, hp] at ha
    | short e => simp [BigCycle.insertedConnector, hp] at ha
    | long e q f =>
        have heq : a = (Sum.inr q : V ⊕ P) := by
          simpa [BigCycle.insertedConnector, hp] using ha.symm
        subst a
        exact (hFresh r e q f hp t).symm
  have hDifferent := C.literal_output_inserts_different
    D B first hWord
  have hRight : oldPos i = cyclicSucc j :=
    C.literal_fresh_successor_oldPos
      D B first hInsertFresh hDifferent hWord oldPos hConnector
      i (Sum.inr p) hNew j hj
  exact ⟨hLeft, hRight⟩

end StructuralRamsey.Girth.OrderOneData
