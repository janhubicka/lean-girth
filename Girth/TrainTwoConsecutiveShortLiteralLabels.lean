import Girth.TrainTwoConsecutiveShortComplete
import Mathlib.Tactic

/-!
# Path A: exact Fin-index label word of a physical two-short replacement

A short-only replacement uses one literal output label at EACH original
source connector, in precisely the original order. This module lifts
the already checked complete two-short theorem to a BigCycle of the
SAME source index type, with explicit output labels at every index.

It is a prerequisite for transporting a two-occurrence geometric owner
assignment and for correctly counting designated labels. No rank
decrease or new geometric admissibility is assumed or claimed.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- The literal output label at each original source index after the
two selected short replacements, including cyclic wrap. -/
def BigCycle.twoConsecutiveShortLabels
    {n : ℕ} (C : D.BigCycle n) (t : Fin n)
    (first second : E) : Fin n → I ⊕ E :=
  fun j => if j = t then Sum.inr first
    else if j = cyclicSucc t then Sum.inr second
    else C.label j

/-- The whole literal two-short replacement word is exactly the
list of new labels paired with the OLD connector at the SAME index.
No incidence or acceptability hypotheses enter this word identity. -/
theorem BigCycle.twoConsecutiveShort_resultWord
    {n : ℕ} (C : D.BigCycle n) (t : Fin n)
    (first second : E) :
    C.resultWord D (C.twoConsecutiveShortPieces D t first second) =
      List.ofFn (fun j : Fin n =>
        (C.twoConsecutiveShortLabels D t first second j,
          C.connector j)) := by
  have hPiece (j : Fin n) :
      C.pieceWord D j (C.twoConsecutiveShortPieces D t first second j) =
        [(C.twoConsecutiveShortLabels D t first second j,
          C.connector j)] := by
    by_cases hJt : j = t
    · subst j
      simp [BigCycle.twoConsecutiveShortPieces,
        BigCycle.twoConsecutiveShortLabels, BigCycle.pieceWord]
    · by_cases hJs : j = cyclicSucc t
      · simp [BigCycle.twoConsecutiveShortPieces,
          BigCycle.twoConsecutiveShortLabels, BigCycle.pieceWord, hJt, hJs]
      · simp [BigCycle.twoConsecutiveShortPieces,
          BigCycle.twoConsecutiveShortLabels, BigCycle.pieceWord, hJt, hJs]
  change (List.ofFn (fun j : Fin n =>
      C.pieceWord D j (C.twoConsecutiveShortPieces D t first second j))).flatten =
    List.ofFn (fun j : Fin n =>
      (C.twoConsecutiveShortLabels D t first second j, C.connector j))
  simp_rw [hPiece]
  exact flatten_ofFn_singleton
    (fun j : Fin n =>
      (C.twoConsecutiveShortLabels D t first second j, C.connector j))

/-- Strengthen the complete physical two-short replacement theorem:
the output has the SAME Fin n index type and the EXACT pointwise
label function. This is independent of original designation count. -/
theorem BigCycle.twoConsecutiveShort_complete_exact_labels
    {n : ℕ} (C : D.BigCycle n)
    (hAccept : C.Acceptable) (hLinear : D.LinearPretrain)
    (hn : 3 ≤ n)
    (t : Fin n) (first second : E)
    (hFirst : D.Incident (.inr first)
        (C.connector (trainCyclicPred t)) ∧
      D.Incident (.inr first) (C.connector t))
    (hSecond : D.Incident (.inr second) (C.connector t) ∧
      D.Incident (.inr second) (C.connector (cyclicSucc t))) :
    ∃ H : D.BigCycle n,
      (∀ j : Fin n,
        H.label j = C.twoConsecutiveShortLabels D t first second j) ∧
      (∀ j : Fin n, H.connector j = C.connector j) ∧
      H.Acceptable ∧ H.twiceOrder = C.twiceOrder ∧
      (∀ jH : Fin n, H.HasSupremeAt D jH →
        ∃ jC : Fin n, C.label jC = H.label jH ∧
          C.HasSupremeAt D jC) := by
  obtain ⟨m, H, hWord, hOutputAccept, hOrder, hPull⟩ :=
    C.twoConsecutiveShort_complete_of_three_le
      D hAccept hLinear hn t first second hFirst hSecond
  have hList :
      List.ofFn (fun j : Fin m => (H.label j, H.connector j)) =
      List.ofFn (fun j : Fin n =>
        (C.twoConsecutiveShortLabels D t first second j,
          C.connector j)) :=
    hWord.trans (C.twoConsecutiveShort_resultWord D t first second)
  have hm : m = n := by
    have h := congrArg List.length hList
    simpa using h
  subst m
  have hPoint (j : Fin n) :
      (H.label j, H.connector j) =
        (C.twoConsecutiveShortLabels D t first second j,
          C.connector j) := by
    have hAt := congrArg
      (fun xs : List ((I ⊕ E) × (V ⊕ P)) => xs[j.val]?) hList
    have hLeft :
        (List.ofFn (fun k : Fin n =>
          (H.label k, H.connector k)))[j.val]? =
          some (H.label j, H.connector j) := by simp [List.get_ofFn]
    have hRight :
        (List.ofFn (fun k : Fin n =>
          (C.twoConsecutiveShortLabels D t first second k,
            C.connector k)))[j.val]? =
          some (C.twoConsecutiveShortLabels D t first second j,
            C.connector j) := by simp [List.get_ofFn]
    exact Option.some.inj (hLeft.symm.trans (hAt.trans hRight))
  refine ⟨H, ?_, ?_, hOutputAccept, hOrder, hPull⟩
  · intro j
    exact congrArg Prod.fst (hPoint j)
  · intro j
    exact congrArg Prod.snd (hPoint j)

end StructuralRamsey.Girth.OrderOneData
