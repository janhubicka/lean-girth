import Girth.CyclicSucc
import Girth.TrainCycleWeights

/-! Extracted from the checked historical CyclicRestriction module; these
lemmas only concern finite cyclic order and the doubled two-sort weight. -/

namespace StructuralRamsey.Girth
namespace ContactCyclicRestriction

/-- The cyclic successor is injective even at the wrap. -/
theorem contactCyclicSucc_injective {n : ℕ} :
    Function.Injective (@cyclicSucc n) := by
  intro i j h
  have hv := congrArg Fin.val h
  change (i.val + 1) % n = (j.val + 1) % n at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  by_cases hi' : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi'] at hv
    by_cases hj' : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj'] at hv
      omega
    · have he : j.val + 1 = n := by omega
      rw [he, Nat.mod_self] at hv
      omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    by_cases hj' : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj'] at hv
      omega
    · omega

private theorem value_lt_of_image_lt {m n : ℕ}
    (f : Fin m ↪o Fin n) {i j : Fin m}
    (h : (f i).val < (f j).val) : i.val < j.val := by
  by_contra hij
  have hji : j ≤ i := by exact Nat.le_of_not_gt hij
  have hmap := f.monotone hji
  change (f j).val ≤ (f i).val at hmap
  omega

/-- An empty increasing gap in the retained image is one cyclic step. -/
private theorem successor_of_increasing_gap {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (hij : (f i).val < (f j).val)
    (hgap : ∀ k : Fin m,
      (f i).val < (f k).val → (f k).val < (f j).val → False) :
    j = cyclicSucc i := by
  have hi : i.val < j.val := value_lt_of_image_lt f hij
  have hiLt : i.val + 1 < m := by omega
  have hnext : j.val = i.val + 1 := by
    by_contra hne
    let k : Fin m := ⟨i.val + 1, hiLt⟩
    have hik : i < k := by change i.val < i.val + 1; omega
    have hkj : k < j := by change i.val + 1 < j.val; omega
    exact hgap k (f.strictMono hik) (f.strictMono hkj)
  apply Fin.ext
  change j.val = (i.val + 1) % m
  rw [Nat.mod_eq_of_lt hiLt]
  exact hnext

/-- An empty wrapping gap has the last and first retained positions as ends. -/
private theorem successor_of_wrapping_gap {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (hmax : ∀ k : Fin m, (f i).val < (f k).val → False)
    (hmin : ∀ k : Fin m, (f k).val < (f j).val → False) :
    j = cyclicSucc i := by
  have hiLast : i.val + 1 = m := by
    by_contra hne
    have hiLt : i.val + 1 < m := by omega
    let k : Fin m := ⟨i.val + 1, hiLt⟩
    have hik : i < k := by change i.val < i.val + 1; omega
    exact hmax k (f.strictMono hik)
  have hjZero : j.val = 0 := by
    by_contra hne
    let k : Fin m := ⟨0, by omega⟩
    have hkj : k < j := by change 0 < j.val; omega
    exact hmin k (f.strictMono hkj)
  apply Fin.ext
  change j.val = (i.val + 1) % m
  rw [hiLast, Nat.mod_self, hjZero]

/-- A source successor which survives deletion is the output successor.
The final-to-initial step is included. -/
theorem successor_of_source_successor {m n : ℕ}
    (f : Fin m ↪o Fin n) (i j : Fin m)
    (h : f j = cyclicSucc (f i)) : j = cyclicSucc i := by
  have hv := congrArg Fin.val h
  change (f j).val = ((f i).val + 1) % n at hv
  by_cases hi : (f i).val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    apply successor_of_increasing_gap f i j
    · omega
    · intro k hleft hright
      omega
  · have hlast : (f i).val + 1 = n := by omega
    rw [hlast, Nat.mod_self] at hv
    apply successor_of_wrapping_gap f i j
    · intro k hk
      have := (f k).isLt
      omega
    · intro k hk
      omega

/-- Deleting cyclic connector positions cannot increase twice-order.
For a retained position whose old successor is also retained the weight
is unchanged.  Otherwise at most one extra unit is charged to that old
successor.  These charged positions are distinct and all are deleted, so
no formal interval partition or list of runs is needed. -/
theorem twiceWeight_restrict_le {m n : ℕ} (hn : 2 ≤ n)
    (f : Fin m ↪o Fin n) (kind : Fin n → CycleConnectorKind) :
    (∑ j : Fin m, twiceOccurrenceWeight (kind (f j))
      (kind (f (cyclicSucc j)))) ≤
    ∑ k : Fin n, twiceOccurrenceWeight (kind k) (kind (cyclicSucc k)) := by
  classical
  let weight : Fin n → ℕ := fun k =>
    twiceOccurrenceWeight (kind k) (kind (cyclicSucc k))
  let retained : Finset (Fin n) := Finset.univ.image f
  let chargedFrom : Finset (Fin m) := Finset.univ.filter
    (fun j => f (cyclicSucc j) ≠ cyclicSucc (f j))
  let charged : Finset (Fin n) := chargedFrom.image (fun j => cyclicSucc (f j))
  have hStep (j : Fin m) :
      twiceOccurrenceWeight (kind (f j)) (kind (f (cyclicSucc j))) ≤
      weight (f j) + if f (cyclicSucc j) ≠ cyclicSucc (f j)
        then weight (cyclicSucc (f j)) else 0 := by
    by_cases h : f (cyclicSucc j) = cyclicSucc (f j)
    · simp [h, weight]
    · rw [ite_eq_left h]
      have hOutput := twiceOccurrenceWeight_le_two
        (kind (f j)) (kind (f (cyclicSucc j)))
      have hFirst := twiceOccurrenceWeight_one_le
        (kind (f j)) (kind (cyclicSucc (f j)))
      have hSecond := twiceOccurrenceWeight_one_le
        (kind (cyclicSucc (f j))) (kind (cyclicSucc (cyclicSucc (f j))))
      change _ ≤ weight (f j) + weight (cyclicSucc (f j))
      dsimp [weight]
      omega
  have hDisjoint : Disjoint retained charged := by
    apply Finset.disjoint_left.mpr
    intro k hkRetained hkCharged
    obtain ⟨i, _hi, hik⟩ := Finset.mem_image.mp hkRetained
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hkCharged
    have hNot := (Finset.mem_filter.mp hj).2
    have hSource : f i = cyclicSucc (f j) := hik.trans hjk.symm
    have hOutput := successor_of_source_successor f j i hSource
    apply hNot
    exact (congrArg f hOutput.symm).trans hSource
  have hRetainedSum :
      (∑ j : Fin m, weight (f j)) = ∑ k ∈ retained, weight k := by
    dsimp [retained]
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact f.injective hij
  have hChargedSum :
      (∑ j : Fin m, if f (cyclicSucc j) ≠ cyclicSucc (f j)
        then weight (cyclicSucc (f j)) else 0) =
      ∑ k ∈ charged, weight k := by
    dsimp [charged]
    rw [Finset.sum_image]
    · simp [chargedFrom, Finset.sum_filter]
    · intro i _ j _ hij
      apply f.injective
      exact contactCyclicSucc_injective hij
  calc
    (∑ j : Fin m, twiceOccurrenceWeight (kind (f j))
        (kind (f (cyclicSucc j)))) ≤
        (∑ j : Fin m, weight (f j)) +
        ∑ j : Fin m, if f (cyclicSucc j) ≠ cyclicSucc (f j)
          then weight (cyclicSucc (f j)) else 0 := by
      simpa only [Finset.sum_add_distrib] using
        (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hStep j))
    _ = ∑ k ∈ retained ∪ charged, weight k := by
      rw [hRetainedSum, hChargedSum, Finset.sum_union hDisjoint]
    _ ≤ ∑ k : Fin n, weight k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by intro k _ _; exact Nat.zero_le _)
    _ = _ := rfl


end ContactCyclicRestriction
end StructuralRamsey.Girth
