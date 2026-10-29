import Girth.TrainPositiveCutStandardTransfer
import Girth.TrainOutputOldPos

/-!
# Circulation Track A: literal label provenance of arbitrary replacements

A reduced witness's supreme gluing copy is not automatically an original
designated source label. The first replacement must ensure that each kept
label and each newly inserted physical edge belongs to the chosen standard.
The checked word computation below turns per-piece provenance into a
statement for EVERY label of the resulting BigCycle (including both labels
of long pieces). No connector-localization or old bound is assumed solved.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Per-piece label provenance implies provenance of the entire literal
output word, without global legality, acceptability or linearity. -/
theorem BigCycle.resultWord_labels_of_piece_property
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (Q : I ⊕ E → Prop)
    (hPiece : ∀ j : Fin n,
      match pieces j with
      | .keep => Q (C.label j)
      | .short e => Q (Sum.inr e)
      | .long e _ f => Q (Sum.inr e) ∧ Q (Sum.inr f)) :
    ∀ entry ∈ C.resultWord D pieces, Q entry.1 := by
  intro entry hEntry
  unfold BigCycle.resultWord at hEntry
  obtain ⟨block, hBlock, hInBlock⟩ := List.mem_flatten.mp hEntry
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hBlock
  cases hp : pieces j with
  | keep =>
      have hOne : entry = (C.label j, C.connector j) := by
        simpa [BigCycle.pieceWord, hp] using hInBlock
      simpa [hOne] using (show Q (C.label j) by
        simpa [hp] using hPiece j)
  | short e =>
      have hOne : entry = (Sum.inr e, C.connector j) := by
        simpa [BigCycle.pieceWord, hp] using hInBlock
      simpa [hOne] using (show Q (Sum.inr e : I ⊕ E) by
        simpa [hp] using hPiece j)
  | long e p f =>
      have hCases :
          entry = (Sum.inr e, Sum.inr p) ∨
          entry = (Sum.inr f, C.connector j) := by
        simpa [BigCycle.pieceWord, hp] using hInBlock
      have hBoth : Q (Sum.inr e) ∧ Q (Sum.inr f) := by
        simpa [hp] using hPiece j
      rcases hCases with hFirst | hLast
      · simpa [hFirst] using hBoth.1
      · simpa [hLast] using hBoth.2

/-- Every actual output label inherits a source-piece provenance, not
merely the output labels at old connector positions. -/
theorem BigCycle.replacement_labels_of_piece_property
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (Q : I ⊕ E → Prop)
    (hPiece : ∀ j : Fin n,
      match pieces j with
      | .keep => Q (C.label j)
      | .short e => Q (Sum.inr e)
      | .long e _ f => Q (Sum.inr e) ∧ Q (Sum.inr f))
    (hWord : List.ofFn (fun k : Fin m =>
        (B.label k, B.connector k)) = C.resultWord D pieces) :
    ∀ k : Fin m, Q (B.label k) := by
  intro k
  have hMem : (B.label k, B.connector k) ∈ C.resultWord D pieces := by
    rw [← hWord]
    exact List.mem_ofFn.mpr ⟨k, rfl⟩
  exact C.resultWord_labels_of_piece_property D pieces Q hPiece _ hMem

/-- The length-at-least-three standard-local supreme transfer, now with
only per-piece physical label provenance. The old bound still requires
the geometric connector and standard transport to be discharged. -/
theorem BigCycle.supreme_of_piecewise_standard_provenance_of_three_le
    {n q : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable)
    (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (hOrder : C.twiceOrder ≤ 2 * q)
    (pieces : Fin n → TrainSupremePiece E P)
    (hInc : C.LocalPieceIncidence D pieces)
    (hGeom : C.LocalLongA2Geometry D pieces)
    (hFresh : ∀ (i : Fin n) (e : E) (p : P) (f : E),
      pieces i = .long e p f →
      ∀ t : Fin n, C.connector t ≠ Sum.inr p)
    (InStandard : (I ⊕ E) → Prop)
    (hPiece : ∀ j : Fin n,
      match pieces j with
      | .keep => InStandard (C.label j)
      | .short e => InStandard (Sum.inr e)
      | .long e _ f =>
          InStandard (Sum.inr e) ∧ InStandard (Sum.inr f))
    (hOldBound : ∀ (m : ℕ) (B : D.BigCycle m),
      (∀ k : Fin m, InStandard (B.label k)) →
      B.Acceptable → B.twiceOrder ≤ 2 * q →
      B.HasSimultaneousSupreme) :
    C.HasSimultaneousSupreme := by
  apply C.supreme_of_arbitrary_replacement_in_standard_of_three_le
    D hAccept hLinear hn hOrder pieces hInc hGeom hFresh
    (fun {m} B => ∀ k : Fin m, InStandard (B.label k))
  · intro m B hWord
    exact C.replacement_labels_of_piece_property
      D B pieces InStandard hPiece hWord
  · exact hOldBound

end StructuralRamsey.Girth.OrderOneData
