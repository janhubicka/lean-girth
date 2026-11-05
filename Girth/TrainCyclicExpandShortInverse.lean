import Girth.TrainCyclicExpandReducedPieces
import Mathlib.Tactic

/-!
# Path A: every short in the source-expanded plan has exact reduced provenance

An original-source physical short has TWO fundamentally different
origins: it can be a genuine short selected by the reduced supreme
plan, or it can be one of the two physical edges of a REDUCED LONG
piece when that long piece spans a non-singleton original source run.

The literal expansion distinguishes the two long halves by their
original positions. At the final original cut position it takes the
SECOND long edge; at every other position of that run it takes
the FIRST. For a singleton long it inserts a physical LONG, not a
short. These facts follow by constructor case splitting alone.

This pure finite interface will be combined with the actual singleton
and two-step reverse run-fibre theorems for source LocalPieceIncidence.
No geometric contact is assumed here. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
universe v
variable {Owner E P F Q : Type v} {n : ℕ}

/-- Exact provenance of an expanded physical short. Either it came
from a reduced SHORT, or from a reduced LONG. In the latter case
its position and mapped edge are precisely determined by whether
the occurrence ends the original owner run.

In particular, a REDUCED singleton-long never produces a source
short at its final cut because both cut boundaries are consecutive;
the formal piece cases retain the exact alignment condition. -/
theorem cyclicExpandReducedPieces_short_inverse
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (pos : Fin n) (a : F)
    (hOut : cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .short a) :
    (∃ (j : Fin (cyclicOwnerChanges owner)) (e : E),
      cyclicOwnerRunIndex owner hCuts pos = j ∧
      reduced j = .short e ∧ edge e = a) ∨
    (∃ (j : Fin (cyclicOwnerChanges owner))
      (first : E) (w : P) (second : E),
      cyclicOwnerRunIndex owner hCuts pos = j ∧
      reduced j = .long first w second ∧
      ((pos = cyclicOwnerCutIndex owner j ∧
        cyclicOwnerCutIndex owner (trainCyclicPred j) ≠
          trainCyclicPred pos ∧
        edge second = a) ∨
       (pos ≠ cyclicOwnerCutIndex owner j ∧
        edge first = a))) := by
  classical
  let j := cyclicOwnerRunIndex owner hCuts pos
  cases hp : reduced j with
  | keep =>
      simp [cyclicExpandReducedPieces, j, hp] at hOut
  | short e =>
      have hMapped :
          (TrainSupremePiece.short (edge e) : TrainSupremePiece F Q) =
            .short a := by
        simpa [cyclicExpandReducedPieces, j, hp] using hOut
      have he : edge e = a := by
        simpa using hMapped
      exact Or.inl ⟨j, e, rfl, hp, he⟩
  | long first w second =>
      by_cases hAt : pos = cyclicOwnerCutIndex owner j
      · by_cases hPrev :
          cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred pos
        · simp [cyclicExpandReducedPieces, j, hp, hAt, hPrev]
            at hOut
        · have hMapped :
              (TrainSupremePiece.short (edge second) :
                TrainSupremePiece F Q) = .short a := by
            simpa [cyclicExpandReducedPieces, j, hp, hAt, hPrev]
              using hOut
          have he : edge second = a := by
            simpa using hMapped
          exact Or.inr ⟨j, first, w, second, rfl, hp,
            Or.inl ⟨hAt, hPrev, he⟩⟩
      · have hMapped :
            (TrainSupremePiece.short (edge first) :
              TrainSupremePiece F Q) = .short a := by
          simpa [cyclicExpandReducedPieces, j, hp, hAt] using hOut
        have he : edge first = a := by
          simpa using hMapped
        exact Or.inr ⟨j, first, w, second, rfl, hp,
          Or.inr ⟨hAt, he⟩⟩

end StructuralRamsey.Girth
