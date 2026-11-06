import Girth.TrainCyclicExpandReducedPieces
import Girth.TrainCyclicRunIndexReverseWindow
import Girth.TrainOneFreshLongPhysical
import Mathlib.Tactic

/-!
# Path A: the run-fibre interface gives physical incidence of the expanded source plan

This is a purely geometric/finite theorem about an arbitrary
OrderOneData BigCycle. It does NOT assume an original source label
equals a chosen reduced geometric owner or chosen designated B-copy.

A reduced SHORT is required to lie over a singleton source run and
be physically incident with that source occurrence's two connectors.
A reduced LONG can either lie over a singleton run and satisfy genuine
PhysicalLongGeometry, or over an exact two-step run with an EXISTING
intermediate connector and two SHORT physical incidences.

The checked reverse run-fibre theorems ensure that those are ALL
source occurrences controlled by each reduced run. Consequently
their literal expanded source plan satisfies LocalPieceIncidence,
including the original cyclic wrap boundary.

The remaining actual selected-picture theorem must derive these
geometric inputs from one fixed PlanValid reduced witness. No appendix.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P Er Wr Owner : Type v} (D : OrderOneData V E I P)

/-- A source-indexed expansion of a reduced owner-run plan has FULL
LocalPieceIncidence once every selected reduced short/long has its
corresponding ORIGINAL singleton or two-step physical geometry.

The source run index and both reverse-fibre bounds are the checked
canonical ones, including cyclic last-to-first wrap. -/
theorem BigCycle.expanded_run_plan_localIncidence
    {n : ℕ} (K : D.BigCycle n)
    (hn : 3 ≤ n)
    (owner : Fin n → Owner)
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece Er Wr)
    (edge : Er → E) (wagon : Wr → P)
    (hShort : ∀ (j : Fin (cyclicOwnerChanges owner)) (e : Er),
      reduced j = .short e →
      ∃ pos : Fin n,
        cyclicOwnerCutIndex owner j = pos ∧
        cyclicOwnerCutIndex owner (trainCyclicPred j) =
          trainCyclicPred pos ∧
        D.Incident (.inr (edge e))
          (K.connector (trainCyclicPred pos)) ∧
        D.Incident (.inr (edge e)) (K.connector pos))
    (hLong : ∀ (j : Fin (cyclicOwnerChanges owner))
      (first : Er) (w : Wr) (second : Er),
      reduced j = .long first w second →
      (∃ pos : Fin n,
        cyclicOwnerCutIndex owner j = pos ∧
        cyclicOwnerCutIndex owner (trainCyclicPred j) =
          trainCyclicPred pos ∧
        K.PhysicalLongGeometry D pos
          (edge first) (wagon w) (edge second)) ∨
      (∃ t : Fin n,
        cyclicOwnerCutIndex owner j = cyclicSucc t ∧
        cyclicOwnerCutIndex owner (trainCyclicPred j) =
          trainCyclicPred t ∧
        owner t = owner (cyclicSucc t) ∧
        (D.Incident (.inr (edge first))
            (K.connector (trainCyclicPred t)) ∧
          D.Incident (.inr (edge first)) (K.connector t)) ∧
        (D.Incident (.inr (edge second)) (K.connector t) ∧
          D.Incident (.inr (edge second))
            (K.connector (cyclicSucc t))))) :
    K.LocalPieceIncidence D
      (cyclicExpandReducedPieces owner (by omega) reduced edge wagon) := by
  classical
  have hPos : 0 < cyclicOwnerChanges owner := by omega
  have hTwo : 2 ≤ cyclicOwnerChanges owner := by omega
  intro pos
  let j := cyclicOwnerRunIndex owner hPos pos
  cases hp : reduced j with
  | keep =>
      simp [BigCycle.LocalPieceIncidence,
        cyclicExpandReducedPieces, j, hp]
  | short e =>
      obtain ⟨p, hHere, hPrev, hLeft, hRight⟩ :=
        hShort j e hp
      have hOnly : pos = p :=
        cyclicOwnerRunIndex_singleton_fibre owner
          (by omega : 2 ≤ n) hTwo j p pos hPrev hHere rfl
      subst pos
      have hExp :
          cyclicExpandReducedPieces owner hPos reduced edge wagon p =
            .short (edge e) :=
        cyclicExpandReducedPieces_short
          owner hPos reduced edge wagon j p
          (by rw [← hHere]; exact cyclicOwnerRunIndex_at_cut owner hPos j)
          e hp
      change (match cyclicExpandReducedPieces
        owner hPos reduced edge wagon p with
        | .keep => True
        | .short a =>
          D.Incident (.inr a) (K.connector (trainCyclicPred p)) ∧
          D.Incident (.inr a) (K.connector p)
        | .long a w b =>
          a ≠ b ∧ D.Incident (.inr a)
            (K.connector (trainCyclicPred p)) ∧
            D.parent a = w ∧ D.parent b = w ∧
            D.Incident (.inr b) (K.connector p))
      rw [hExp]
      exact ⟨hLeft, hRight⟩
  | long first w second =>
      rcases hLong j first w second hp with
        ⟨p, hHere, hPrev, hPhysical⟩ |
        ⟨t, hHere, hPrev, hUncut, hFirstInc, hSecondInc⟩
      · have hOnly : pos = p :=
          cyclicOwnerRunIndex_singleton_fibre owner
            (by omega : 2 ≤ n) hTwo j p pos hPrev hHere rfl
        subst pos
        have hExp :
            cyclicExpandReducedPieces owner hPos reduced edge wagon p =
              .long (edge first) (wagon w) (edge second) :=
          cyclicExpandReducedPieces_long_singleton
            owner hPos reduced edge wagon j p hHere hPrev
            first second w hp
        obtain ⟨x, y, hLeft, hRight, hNe, hParentFirst,
          hParentSecond, hx, hy, _hNoPair⟩ := hPhysical
        change (match cyclicExpandReducedPieces
          owner hPos reduced edge wagon p with
          | .keep => True
          | .short a =>
              D.Incident (.inr a) (K.connector (trainCyclicPred p)) ∧
              D.Incident (.inr a) (K.connector p)
          | .long a q b =>
              a ≠ b ∧
              D.Incident (.inr a) (K.connector (trainCyclicPred p)) ∧
              D.parent a = q ∧ D.parent b = q ∧
              D.Incident (.inr b) (K.connector p))
        rw [hExp]
        refine ⟨hNe, ?_, hParentFirst, hParentSecond, ?_⟩
        · rw [hLeft]
          exact hx
        · rw [hRight]
          exact hy
      · have hOnly : pos = t ∨ pos = cyclicSucc t :=
          cyclicOwnerRunIndex_two_step_fibre
            owner hn hThree j t pos hPrev hHere rfl
        have hExp :=
          cyclicExpandReducedPieces_long_two_step
            owner hn hPos reduced edge wagon j t
            hUncut hPrev hHere first second w hp
        rcases hOnly with hAtT | hAtSucc
        · subst pos
          change (match cyclicExpandReducedPieces
            owner hPos reduced edge wagon t with
            | .keep => True
            | .short a =>
                D.Incident (.inr a) (K.connector (trainCyclicPred t)) ∧
                D.Incident (.inr a) (K.connector t)
            | .long a q b =>
                a ≠ b ∧
                D.Incident (.inr a)
                  (K.connector (trainCyclicPred t)) ∧
                D.parent a = q ∧ D.parent b = q ∧
                D.Incident (.inr b) (K.connector t))
          rw [hExp.1]
          exact hFirstInc
        · subst pos
          change (match cyclicExpandReducedPieces
            owner hPos reduced edge wagon (cyclicSucc t) with
            | .keep => True
            | .short a =>
                D.Incident (.inr a)
                  (K.connector (trainCyclicPred (cyclicSucc t))) ∧
                D.Incident (.inr a) (K.connector (cyclicSucc t))
            | .long a q b =>
                a ≠ b ∧
                D.Incident (.inr a)
                  (K.connector (trainCyclicPred (cyclicSucc t))) ∧
                D.parent a = q ∧ D.parent b = q ∧
                D.Incident (.inr b) (K.connector (cyclicSucc t)))
          rw [hExp.2]
          simpa only [trainCyclicPred_cyclicSucc_of_two_le
            (by omega : 2 ≤ n) t] using hSecondInc

end OrderOneData
end StructuralRamsey.Girth
