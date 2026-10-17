import Girth.TrainOutputOldPos
import Girth.TrainOutputWagonOrigin
import Girth.TrainLiteralOutputA2

/-!
# Circulation: exact occurrence labels in a literal replacement output

The oldPos map is already checked on physical CONNECTORS. To compose
later supreme pieces we also need the labels at those positions.
The final entry of each source replacement block has its original
connector and its pieceLastLabel; connector injectivity identifies
that entry uniquely with oldPos.

For a long piece, its inserted wagon position carries precisely the
first chosen physical edge label. These are exact literal-word facts,
without any fixed supreme target, PlanValid, acceptability, or
appendix input.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The output label at an inherited original right connector is
exactly the final label of that source replacement block. -/
theorem BigCycle.literal_oldPos_label
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n) :
    B.label (oldPos i) =
      C.pieceLastLabel D (C.label i) (pieces i) := by
  have hMem :
      (C.pieceLastLabel D (C.label i) (pieces i),
        C.connector i) ∈ C.resultWord D pieces := by
    unfold BigCycle.resultWord
    apply List.mem_flatten.mpr
    refine ⟨C.pieceWord D i (pieces i),
      List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    cases hp : pieces i with
    | keep => simp [BigCycle.pieceWord, BigCycle.pieceLastLabel, hp]
    | short e => simp [BigCycle.pieceWord, BigCycle.pieceLastLabel, hp]
    | long e p f => simp [BigCycle.pieceWord, BigCycle.pieceLastLabel, hp]
  have hOut :
      (C.pieceLastLabel D (C.label i) (pieces i),
        C.connector i) ∈
        List.ofFn (fun t : Fin m => (B.label t, B.connector t)) := by
    rw [hWord]
    exact hMem
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hOut
  have hc : B.connector j = C.connector i :=
    congrArg Prod.snd hj
  have eqJ : j = oldPos i :=
    B.connector_injective (hc.trans (hConnector i).symm)
  have hl : B.label j =
      C.pieceLastLabel D (C.label i) (pieces i) :=
    congrArg Prod.fst hj
  simpa [eqJ] using hl

/-- A kept source label survives at the exact oldPos index. -/
theorem BigCycle.literal_keep_label
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n) (hKeep : pieces i = .keep) :
    B.label (oldPos i) = C.label i := by
  simpa [BigCycle.pieceLastLabel, hKeep] using
    (C.literal_oldPos_label D B pieces hWord oldPos hConnector i)

/-- The last output occurrence of a long piece carries its second
chosen physical edge, exactly at its original oldPos. -/
theorem BigCycle.literal_long_last_label
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (i : Fin n) (e f : E) (p : P)
    (hLong : pieces i = .long e p f) :
    B.label (oldPos i) = Sum.inr f := by
  simpa [BigCycle.pieceLastLabel, hLong] using
    (C.literal_oldPos_label D B pieces hWord oldPos hConnector i)

/-- The first physical edge label of each long piece occurs at its
fresh inserted wagon connector. This is a precise label-and-connector
statement, not just a support-membership assertion. -/
theorem BigCycle.literal_long_first_entry
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun t : Fin m =>
      (B.label t, B.connector t)) = C.resultWord D pieces)
    (i : Fin n) (e f : E) (p : P)
    (hLong : pieces i = .long e p f) :
    ∃ j : Fin m,
      B.label j = Sum.inr e ∧ B.connector j = Sum.inr p := by
  have hMem :
      ((Sum.inr e : I ⊕ E), (Sum.inr p : V ⊕ P)) ∈
        C.resultWord D pieces := by
    unfold BigCycle.resultWord
    apply List.mem_flatten.mpr
    refine ⟨C.pieceWord D i (pieces i),
      List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    simp [BigCycle.pieceWord, hLong]
  have hOut :
      ((Sum.inr e : I ⊕ E), (Sum.inr p : V ⊕ P)) ∈
        List.ofFn (fun t : Fin m => (B.label t, B.connector t)) := by
    rw [hWord]
    exact hMem
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hOut
  exact ⟨j, congrArg Prod.fst hj, congrArg Prod.snd hj⟩

end StructuralRamsey.Girth.OrderOneData
