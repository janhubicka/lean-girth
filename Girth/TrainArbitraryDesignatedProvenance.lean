import Girth.TrainOutputOldPos
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Circulation: designated label provenance under arbitrary literal replacements

The general admissible-replacement lemma permits keeping arbitrary
designated occurrences, unlike the strict PlanValid supreme collapse.

Nevertheless each piece contributes either its original labelled
occurrence (keep), one actual edge label (short), or two actual edge
labels (long). Therefore a designated label in the literal expanded
word necessarily comes from a KEPT original occurrence, with exactly
its original physical right connector.

This statement is independent of source acceptability, PlanValid,
freshness, linearity, output A1--A3, and all appendix hypotheses.
It gives the source index required to compose a later supreme label.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- In any individual replacement block, a designated label can only
be the unchanged label of a kept source occurrence. -/
theorem BigCycle.designated_pieceWord_from_keep
    {n : ℕ} (C : D.BigCycle n)
    (i : Fin n) (piece : TrainSupremePiece E P)
    (a : I ⊕ E) (q : V ⊕ P)
    (hDes : D.designated a)
    (hMem : (a, q) ∈ C.pieceWord D i piece) :
    piece = .keep ∧ C.label i = a ∧ C.connector i = q := by
  cases piece with
  | keep =>
      have hEq : (a, q) = (C.label i, C.connector i) := by
        simpa [BigCycle.pieceWord] using hMem
      exact ⟨rfl, (congrArg Prod.fst hEq).symm,
        (congrArg Prod.snd hEq).symm⟩
  | short e =>
      cases a with
      | inl u =>
          have hBad : False := by
            simpa [BigCycle.pieceWord] using hMem
          exact False.elim hBad
      | inr e =>
          simp [designated] at hDes
  | long e p f =>
      cases a with
      | inl u =>
          have hBad : False := by
            simpa [BigCycle.pieceWord] using hMem
          exact False.elim hBad
      | inr e =>
          simp [designated] at hDes

/-- A designated entry anywhere in the FULL replacement word comes
from exactly one original kept occurrence. No legality assumptions
on the replacement plan are needed. -/
theorem BigCycle.designated_resultWord_from_keep
    {n : ℕ} (C : D.BigCycle n)
    (pieces : Fin n → TrainSupremePiece E P)
    (a : I ⊕ E) (q : V ⊕ P)
    (hDes : D.designated a)
    (hMem : (a, q) ∈ C.resultWord D pieces) :
    ∃ i : Fin n,
      pieces i = .keep ∧ C.label i = a ∧ C.connector i = q := by
  unfold BigCycle.resultWord at hMem
  obtain ⟨block, hBlock, hInside⟩ := List.mem_flatten.mp hMem
  obtain ⟨i, hEq⟩ := List.mem_ofFn.mp hBlock
  refine ⟨i, ?_⟩
  exact C.designated_pieceWord_from_keep D i (pieces i)
    a q hDes (by simpa [hEq] using hInside)

/-- Any designated label appearing in a legal literal output BigCycle
identifies an original kept occurrence with the same label and
connector. In particular the designated label was not created. -/
theorem BigCycle.output_designated_from_kept_source
    {n m : ℕ} (C : D.BigCycle n) (B : D.BigCycle m)
    (pieces : Fin n → TrainSupremePiece E P)
    (hWord : List.ofFn (fun j : Fin m =>
      (B.label j, B.connector j)) = C.resultWord D pieces)
    (j : Fin m) (hDes : D.designated (B.label j)) :
    ∃ i : Fin n,
      pieces i = .keep ∧
      C.label i = B.label j ∧
      C.connector i = B.connector j := by
  have hMem : (B.label j, B.connector j) ∈ C.resultWord D pieces := by
    rw [← hWord]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  exact C.designated_resultWord_from_keep
    D pieces (B.label j) (B.connector j) hDes hMem

end StructuralRamsey.Girth.OrderOneData
