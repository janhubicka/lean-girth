import Girth.TrainNoInsertionStageCompose
import Girth.TrainWagonBoundaryShort
import Girth.TrainTwoStageLongComposition
import Girth.TrainLiteralPieceLabels
import Girth.TrainOptionalFreshnessConverse
import Girth.TrainFreshLocalSupreme
import Girth.TrainArbitraryDesignatedOrigin

/-!
# Circulation: composing a later supreme copy through an arbitrary first replacement

Let the first arbitrary replacement be a genuine literal BigCycle, with
each first long piece satisfying the physical two-boundary and nonedge
condition. Suppose the output has an indexed supreme label. That label
is a kept source label. For every other original source occurrence:

* if the first piece inserted nothing, transport the later piece at
  oldPos back across the unchanged original boundary;
* if the first piece was long, its two output edges both require
  later shorts, and their bridges compose to a source long piece.

In both cases all long witnesses are fresh against the original source
connector word. The checked fresh-local-witness construction assembles
a genuine source supreme replacement. This is the full COMPOSITION
assertion of the broad admissible-replacement lemma, conditional on
the first output already being a legal BigCycle.

No appendix theorem, later output acceptability, or assumed global
composed PlanValid is used.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- An original occurrence with a different label from the target
cannot acquire that target as its literal output oldPos label:
designated output labels come exclusively from kept original entries. -/
theorem BigCycle.nonselected_oldPos_label_ne_target
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (first : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D first)
    (oldPos : Fin n → Fin m)
    (hConnector : ∀ i : Fin n,
      B.connector (oldPos i) = C.connector i)
    (kC : Fin n) (kB : Fin m)
    (hTarget : B.label kB = C.label kC)
    (hSelected : D.designated (B.label kB))
    (i : Fin n) (hNe : C.label i ≠ C.label kC) :
    B.label (oldPos i) ≠ B.label kB := by
  intro hSame
  have hDes : D.designated (B.label (oldPos i)) := by
    rw [hSame]
    exact hSelected
  obtain ⟨t, hPos, _hKept, hLabel⟩ :=
    C.output_designated_origin_of_literalWord
      D B first hWord oldPos hConnector (oldPos i) hDes
  have hit : i = t := by
    apply C.connector_injective
    calc
      C.connector i = B.connector (oldPos i) := (hConnector i).symm
      _ = B.connector (oldPos t) := congrArg B.connector hPos
      _ = C.connector t := hConnector t
  apply hNe
  calc
    C.label i = C.label t := congrArg C.label hit
    _ = B.label (oldPos i) := hLabel
    _ = B.label kB := hSame
    _ = C.label kC := hTarget

/-- A later supreme label of an arbitrary locally geometric literal
output is already supreme in the original acceptable source cycle.
The proof constructs and assembles all physical source witnesses. -/
theorem BigCycle.supreme_of_arbitrary_literal_replacement
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (first : Fin n → TrainSupremePiece E P)
    (hGeom : C.LocalLongA2Geometry D first)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D first)
    (kB : Fin m) (hSupreme : B.HasSupremeAt D kB) :
    ∃ kC : Fin n,
      C.label kC = B.label kB ∧ C.HasSupremeAt D kC := by
  obtain ⟨kC, hLabelC⟩ :=
    C.supreme_target_occurs_in_source D B first hWord kB hSupreme
  let hTarget : B.label kB = C.label kC := hLabelC.symm
  have hkC : D.designated (C.label kC) := by
    rw [← hTarget]
    exact hSupreme.1
  obtain ⟨oldPos, hConnector, _hVertexPos⟩ :=
    C.oldPos_exists_of_literal_resultWord D B first hWord
  have hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      first i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p :=
    C.longWagons_fresh_of_literalBigCycle D B first hWord
  obtain ⟨later, hPlan, _hLaterOutput, hLaterFresh⟩ :=
    B.freshness_of_hasSupremeAt D kB hSupreme
  have hLocal : ∀ i : Fin n, C.label i ≠ C.label kC →
      (∃ e : E, C.ShortValid D kC i e) ∨
      (∃ (e f : E) (p : P),
        C.LongValid D kC i e p f ∧
        ∀ t : Fin n, C.connector t ≠ Sum.inr p) := by
    intro i hNe
    have hOutNe : B.label (oldPos i) ≠ B.label kB :=
      C.nonselected_oldPos_label_ne_target
        D B first hWord oldPos hConnector kC kB
        hTarget hSupreme.1 i hNe
    cases hp : first i with
    | keep =>
        have hNone : C.insertedConnector D first i = none := by
          simp [BigCycle.insertedConnector, hp]
        exact C.local_witness_of_later_noInsertion
          D B first hFresh hWord oldPos hConnector
          kC kB hTarget later hPlan hLaterFresh i hNone hOutNe
    | short e =>
        have hNone : C.insertedConnector D first i = none := by
          simp [BigCycle.insertedConnector, hp]
        exact C.local_witness_of_later_noInsertion
          D B first hFresh hWord oldPos hConnector
          kC kB hTarget later hPlan hLaterFresh i hNone hOutNe
    | long e p f =>
        obtain ⟨j, hBLabel, hBJ⟩ :=
          C.literal_long_first_entry D B first hWord i e f p hp
        have hJNe : B.label j ≠ B.label kB := by
          intro hSame
          have hDes : D.designated (B.label j) := by
            rw [hSame]
            exact hSupreme.1
          rw [hBLabel] at hDes
          cases hDes
        obtain ⟨g, _hgPiece, hg⟩ :=
          B.short_piece_of_wagon_right
            D kB j later hPlan hJNe p hBJ
        obtain ⟨_hPrevPos, hNextPos⟩ :=
          C.literal_long_fresh_neighbours D B first hFresh
            hWord oldPos hConnector i e f p hp j hBJ
        have hPredJ : trainCyclicPred (oldPos i) = j := by
          have heq := congrArg trainCyclicPred hNextPos
          simpa [trainCyclicPred_cyclicSucc_of_two_le
            B.length_ge_two j] using heq
        have hWagonBefore : B.connector
            (trainCyclicPred (oldPos i)) = Sum.inr p := by
          rw [hPredJ]
          exact hBJ
        obtain ⟨h, _hhPiece, hh⟩ :=
          B.short_piece_of_wagon_left
            D kB (oldPos i) later hPlan hOutNe p hWagonBefore
        obtain ⟨a, b, hLong⟩ :=
          C.compose_first_long_from_two_later_shorts
            D B first hGeom hFresh hWord oldPos hConnector
            kC kB hTarget i e f p hp j hBJ g h hg hh
        exact Or.inr ⟨a, b, p, hLong, hFresh i e p f hp⟩
  exact ⟨kC, hLabelC,
    C.hasSupremeAt_of_fresh_local_witnesses
      D hAccept hLinear kC hkC hLocal⟩

end StructuralRamsey.Girth.OrderOneData
