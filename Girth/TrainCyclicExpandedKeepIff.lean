import Girth.TrainCyclicExpandReducedPieces
import Mathlib.Tactic

/-!
# Path A: the source-expanded plan keeps exactly the reduced-kept runs

The expansion of a fixed reduced plan never introduces an accidental
`.keep`: an original occurrence is kept if and only if its canonical
reduced run piece is itself `.keep`. This is a literal constructor
statement, requiring no physical geometry or selected standard.

Combined with the independent fixed-plan ownership theorem in
TrainActualPlanKeptRunOwner (#846), it supplies the `hKeep` input
for the already verified standard-contained replacement transfer.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner E P F Q : Type v} {n : ℕ}

/-- A physical source occurrence is kept by the expanded
source-indexed plan EXACTLY when the specified reduced plan keeps
its canonical owner-run index. This is true for singleton longs,
two-step longs, shorts and cyclic wrap, with no distinct-owner
assumptions at remote runs. -/
theorem cyclicExpandReducedPieces_keep_iff
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (pos : Fin n) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon pos = .keep ↔
      reduced (cyclicOwnerRunIndex owner hCuts pos) = .keep := by
  constructor
  · intro h
    let j := cyclicOwnerRunIndex owner hCuts pos
    cases hp : reduced j with
    | keep =>
        rfl
    | short e =>
        have hNot :
            cyclicExpandReducedPieces owner hCuts reduced edge wagon pos ≠
              (.keep : TrainSupremePiece F Q) := by
          simp [cyclicExpandReducedPieces, j, hp]
        exact False.elim (hNot h)
    | long first w second =>
        have hNot :
            cyclicExpandReducedPieces owner hCuts reduced edge wagon pos ≠
              (.keep : TrainSupremePiece F Q) := by
          simp [cyclicExpandReducedPieces, j, hp] <;> split_ifs <;> simp
        exact False.elim (hNot h)
  · intro h
    exact cyclicExpandReducedPieces_keep owner hCuts reduced edge wagon
      (cyclicOwnerRunIndex owner hCuts pos) pos rfl h

end StructuralRamsey.Girth
