import Girth.TrainCyclicRunIndexUncutSuccessor
import Girth.TrainActualThreeCutNonadjacentLong
import Mathlib.Tactic

/-!
# Path A: literal source-indexed expansion of a reduced owner-run plan

This is a PURE FINITE TRANSLATION of a reduced cut-indexed
TrainSupremePiece word back to ORIGINAL source positions.

Every original occurrence is assigned to the canonical maximal owner
run by the wrap-aware run index. A reduced keep stays keep, a reduced
short becomes a physical short, and a reduced long becomes:
* a physical long at a singleton original run;
* a physical first short at a non-cut interior source occurrence;
* a physical second short at the final cut of a non-singleton run.

The exact singleton and two-step formulas are proved below. No physical
edge incidence, actual output BigCycle, global supreme plan, or descent
is assumed or claimed. Those are separate proof obligations.
Circulation only, no appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner E P F Q : Type v} {n : ℕ}

/-- A canonical source-indexed plan obtained from a selected REDUCED
owner-run plan. The two tests for a reduced long piece distinguish:
(a) the final source position of the run, and (b) a singleton run.
A non-singleton final position uses the second short edge; interior
source positions use the first. This is deliberately a total function
even before proving that all non-target runs have width ≤ 2. -/
noncomputable def cyclicExpandReducedPieces
    (owner : Fin n → Owner) (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (pos : Fin n) : TrainSupremePiece F Q := by
  classical
  let j := cyclicOwnerRunIndex owner hCuts pos
  exact match reduced j with
    | .keep => .keep
    | .short e => .short (edge e)
    | .long first w second =>
      if pos = cyclicOwnerCutIndex owner j then
        if cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred pos then
          .long (edge first) (wagon w) (edge second)
        else
          .short (edge second)
      else
        .short (edge first)

/-- Keeping a reduced run keeps every original occurrence of that run,
without any claim that its original LABEL is the same as the reduced
standard owner value. -/
theorem cyclicExpandReducedPieces_keep
    (owner : Fin n → Owner) (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (j : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hRun : cyclicOwnerRunIndex owner hCuts pos = j)
    (hPiece : reduced j = .keep) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .keep := by
  simp [cyclicExpandReducedPieces, hRun, hPiece]

/-- A reduced short produces the same physical short at every source
position assigned to its run (the actual supreme argument later shows
this run must be singleton). -/
theorem cyclicExpandReducedPieces_short
    (owner : Fin n → Owner) (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (j : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hRun : cyclicOwnerRunIndex owner hCuts pos = j)
    (e : E) (hPiece : reduced j = .short e) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .short (edge e) := by
  simp [cyclicExpandReducedPieces, hRun, hPiece]

/-- A singleton original run translates a reduced long into a genuine
one-occurrence physical long insertion with mapped wagon. -/
theorem cyclicExpandReducedPieces_long_singleton
    (owner : Fin n → Owner) (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (j : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hHere : cyclicOwnerCutIndex owner j = pos)
    (hPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) =
      trainCyclicPred pos)
    (first second : E) (w : P)
    (hPiece : reduced j = .long first w second) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .long (edge first) (wagon w) (edge second) := by
  have hRun : cyclicOwnerRunIndex owner hCuts pos = j := by
    rw [← hHere]
    exact cyclicOwnerRunIndex_at_cut owner hCuts j
  simp [cyclicExpandReducedPieces, hRun, hHere, hPrev, hPiece]

/-- A noncut source occurrence in a long run takes its FIRST edge as
a physical short, leaving the original right connector in place. -/
theorem cyclicExpandReducedPieces_long_interior
    (owner : Fin n → Owner) (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (j : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hRun : cyclicOwnerRunIndex owner hCuts pos = j)
    (hNotCut : pos ≠ cyclicOwnerCutIndex owner j)
    (first second : E) (w : P)
    (hPiece : reduced j = .long first w second) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .short (edge first) := by
  simp [cyclicExpandReducedPieces, hRun, hNotCut, hPiece]

/-- The LAST source occurrence of a non-singleton long run takes its
SECOND edge as a physical short. No fresh wagon is inserted. -/
theorem cyclicExpandReducedPieces_long_nonsingleton_final
    (owner : Fin n → Owner) (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (j : Fin (cyclicOwnerChanges owner)) (pos : Fin n)
    (hHere : cyclicOwnerCutIndex owner j = pos)
    (hNotPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) ≠
      trainCyclicPred pos)
    (first second : E) (w : P)
    (hPiece : reduced j = .long first w second) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .short (edge second) := by
  have hRun : cyclicOwnerRunIndex owner hCuts pos = j := by
    rw [← hHere]
    exact cyclicOwnerRunIndex_at_cut owner hCuts j
  simp [cyclicExpandReducedPieces, hRun, hHere, hNotPrev, hPiece]

/-- Both source occurrences of a genuine two-step original run use
the two selected reduced-long physical edges as consecutive SHORT
pieces. The middle original wagon connector is left unchanged.

The hypotheses are exactly the old-wagon two-step alignment produced
by the checked Path A physical-long theorem. -/
theorem cyclicExpandReducedPieces_long_two_step
    (owner : Fin n → Owner) (hn : 3 ≤ n)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (j : Fin (cyclicOwnerChanges owner)) (t : Fin n)
    (hUncut : owner t = owner (cyclicSucc t))
    (hPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) =
      trainCyclicPred t)
    (hHere : cyclicOwnerCutIndex owner j = cyclicSucc t)
    (first second : E) (w : P)
    (hPiece : reduced j = .long first w second) :
    cyclicExpandReducedPieces owner hCuts reduced edge wagon t =
      .short (edge first) ∧
    cyclicExpandReducedPieces owner hCuts reduced edge wagon
      (cyclicSucc t) = .short (edge second) := by
  have hAtNext : cyclicOwnerRunIndex owner hCuts (cyclicSucc t) = j := by
    rw [← hHere]
    exact cyclicOwnerRunIndex_at_cut owner hCuts j
  have hAtT : cyclicOwnerRunIndex owner hCuts t = j :=
    (cyclicOwnerRunIndex_succ_of_uncut owner hCuts t hUncut).symm.trans hAtNext
  have hNotT : t ≠ cyclicOwnerCutIndex owner j := by
    rw [hHere]
    exact cyclicSucc_ne_self_of_two_le (by omega : 2 ≤ n) t |>.symm
  have hPredNeT : trainCyclicPred t ≠ t := by
    intro heq
    have hSucc := cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) t
    rw [heq] at hSucc
    exact (cyclicSucc_ne_self_of_two_le
      (by omega : 2 ≤ n) t) hSucc
  have hNotPrev : cyclicOwnerCutIndex owner (trainCyclicPred j) ≠
      trainCyclicPred (cyclicSucc t) := by
    rw [hPrev, trainCyclicPred_cyclicSucc_of_two_le
      (by omega : 2 ≤ n) t]
    exact hPredNeT
  exact ⟨cyclicExpandReducedPieces_long_interior
      owner hCuts reduced edge wagon j t hAtT hNotT first second w hPiece,
    cyclicExpandReducedPieces_long_nonsingleton_final
      owner hCuts reduced edge wagon j (cyclicSucc t)
      hHere hNotPrev first second w hPiece⟩

end StructuralRamsey.Girth
