import Girth.TrainCyclicOwnerFinListBridge
import Girth.TrainBigCycleOrderOneExtraction
import Mathlib.Tactic

/-!
# A direct cyclic owner-cut budget, without constructing segment blocks

At each source connector i, let c_i be the indicator of an owner
change, and w_i the twice-weight of the connector kind transition.
If an occurrence at i+1 has cuts on both sides, its connector kinds
must agree. Hence c_i + c_(i+1) <= w_i pointwise.

Summing cyclically gives 2 * (# cuts) <= twiceOrder. This bypasses
the earlier explicit CycleReductionBlock decomposition for the
BOTTOM forest count. The literal geometric reduct still needs to
be constructed separately, as does its global supreme transfer.
-/

namespace StructuralRamsey.Girth

universe v

/-- Pure finite cyclic arithmetic. The only exceptional configuration
is TWO consecutive owner cuts with a mixed connector-kind transition.
No minimum assumption or actual hypergraph is used. -/
theorem twice_cyclicOwnerChanges_le_kindWeight
    {Owner : Type v} {n : ℕ}
    (hn : 2 ≤ n)
    (owner : Fin n → Owner)
    (kind : Fin n → CycleConnectorKind)
    (hNoMixed : ∀ k : Fin n,
      owner (trainCyclicPred k) ≠ owner k →
      owner k ≠ owner (cyclicSucc k) →
      kind (trainCyclicPred k) = kind k) :
    2 * cyclicOwnerChanges owner ≤
      ∑ j : Fin n,
        twiceOccurrenceWeight (kind j) (kind (cyclicSucc j)) := by
  classical
  let cut : Fin n → ℕ := fun j =>
    ownerCutStep (owner j) (owner (cyclicSucc j))
  have hLocal (j : Fin n) :
      cut j + cut (cyclicSucc j) ≤
        twiceOccurrenceWeight (kind j) (kind (cyclicSucc j)) := by
    change ownerCutStep (owner j) (owner (cyclicSucc j)) +
        ownerCutStep (owner (cyclicSucc j))
          (owner (cyclicSucc (cyclicSucc j))) ≤
        twiceOccurrenceWeight (kind j) (kind (cyclicSucc j))
    by_cases hFirst : owner j = owner (cyclicSucc j)
    · by_cases hSecond :
        owner (cyclicSucc j) = owner (cyclicSucc (cyclicSucc j))
      · simp [ownerCutStep, hFirst, hSecond]
      · simpa [ownerCutStep, hFirst, hSecond] using
          (twiceOccurrenceWeight_one_le (kind j) (kind (cyclicSucc j)))
    · by_cases hSecond :
        owner (cyclicSucc j) = owner (cyclicSucc (cyclicSucc j))
      · simpa [ownerCutStep, hFirst, hSecond] using
          (twiceOccurrenceWeight_one_le (kind j) (kind (cyclicSucc j)))
      · have hPrev : trainCyclicPred (cyclicSucc j) = j :=
          trainCyclicPred_cyclicSucc_of_two_le hn j
        have hKinds : kind j = kind (cyclicSucc j) := by
          have h := hNoMixed (cyclicSucc j)
            (by simpa only [hPrev] using hFirst) hSecond
          simpa only [hPrev] using h
        simp [ownerCutStep, hFirst, hSecond,
          twiceOccurrenceWeight, hKinds]
  let shift : Fin n ≃ Fin n := {
    toFun := cyclicSucc
    invFun := trainCyclicPred
    left_inv := trainCyclicPred_cyclicSucc_of_two_le hn
    right_inv := cyclicSucc_trainCyclicPred_of_two_le hn
  }
  have hShift :
      (∑ j : Fin n, cut (cyclicSucc j)) =
        (∑ j : Fin n, cut j) := by
    apply Fintype.sum_equiv shift (fun j => cut (cyclicSucc j)) cut
    intro j
    rfl
  have hCutSum :
      (∑ j : Fin n, cut j) = cyclicOwnerChanges owner := by
    change (∑ j : Fin n,
      ownerCutStep (owner j) (owner (cyclicSucc j))) =
        cyclicOwnerChanges owner
    exact (cyclicOwnerChanges_eq_sum_ownerCutStep owner).symm
  have hShiftSum :
      (∑ j : Fin n, cut (cyclicSucc j)) =
        cyclicOwnerChanges owner := hShift.trans hCutSum
  calc
    2 * cyclicOwnerChanges owner =
        (∑ j : Fin n, cut j) + (∑ j : Fin n, cut (cyclicSucc j)) := by
          rw [hCutSum, hShiftSum]
          omega
    _ = ∑ j : Fin n, (cut j + cut (cyclicSucc j)) := by
          rw [Finset.sum_add_distrib]
    _ ≤ ∑ j : Fin n,
        twiceOccurrenceWeight (kind j) (kind (cyclicSucc j)) :=
          Finset.sum_le_sum (by intro j _; exact hLocal j)

namespace OrderOneData

universe w
variable {V E I P : Type w} (D : OrderOneData V E I P)

/-- Direct order budget for a genuine BigCycle and a geometric owner
word whose isolated segments never have mixed connector kinds. -/
theorem BigCycle.twice_ownerCuts_le_twiceOrder_of_no_mixed
    {n : ℕ} (C : D.BigCycle n)
    {Owner : Type v} (owner : Fin n → Owner)
    (hNoMixed : ∀ k : Fin n,
      owner (trainCyclicPred k) ≠ owner k →
      owner k ≠ owner (cyclicSucc k) →
      connectorKind (C.connector (trainCyclicPred k)) =
        connectorKind (C.connector k)) :
    2 * cyclicOwnerChanges owner ≤ C.twiceOrder := by
  exact twice_cyclicOwnerChanges_le_kindWeight C.length_ge_two
    owner (fun j => connectorKind (C.connector j)) hNoMixed

/-- What the bottom forest proof actually needs: the reduced cycle
has exactly the number of geometric owner cuts. Its length is
therefore at most the original source order, without explicit blocks. -/
theorem BigCycle.ownerCuts_le_cutoff_of_no_mixed
    {n q : ℕ} (C : D.BigCycle n)
    {Owner : Type v} (owner : Fin n → Owner)
    (hNoMixed : ∀ k : Fin n,
      owner (trainCyclicPred k) ≠ owner k →
      owner k ≠ owner (cyclicSucc k) →
      connectorKind (C.connector (trainCyclicPred k)) =
        connectorKind (C.connector k))
    (hOrder : C.twiceOrder ≤ 2 * q) :
    cyclicOwnerChanges owner ≤ q := by
  have hCuts := C.twice_ownerCuts_le_twiceOrder_of_no_mixed
    D owner hNoMixed
  omega

end OrderOneData
end StructuralRamsey.Girth
