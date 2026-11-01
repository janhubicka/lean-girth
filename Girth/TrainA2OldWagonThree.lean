import Girth.TrainActualPositiveCutLongWagonExisting
import Girth.TrainCyclicOwnerAbsorption
import Mathlib.Tactic

/-!
# Source A2 restricts an old-wagon adjacent long piece to length three

A real long piece may contact two consecutive ORIGINAL vertex
connectors of an old source wagon. If that wagon is itself a source
connector, A2 says the only vertex positions meeting it lie at its
predecessor or successor. These positions are consecutive exactly
for source length THREE (source length >=3).

The proof is a pure finite cyclic-index argument followed by A2.
It does not presume output freshness or a globally chosen supreme
plan; those are checked separately by #725/#730 and selected-plan
integration. This is the missing source A2 exception bound.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

/-- The cyclic successor is the next numeral, or wraps to zero. -/
private theorem cyclicSucc_val_if {n : ℕ} (i : Fin n) :
    (cyclicSucc i).val =
      if i.val + 1 < n then i.val + 1 else 0 := by
  change (i.val + 1) % n =
    if i.val + 1 < n then i.val + 1 else 0
  by_cases h : i.val + 1 < n
  · simp only [if_pos h]
    exact Nat.mod_eq_of_lt h
  · simp only [if_neg h]
    have hLast : i.val + 1 = n := by omega
    rw [hLast, Nat.mod_self]

/-- The cyclic predecessor is the preceding numeral, or wraps
zero to the last index. -/
private theorem trainCyclicPred_val_if {n : ℕ}
    (i : Fin n) :
    (trainCyclicPred i).val =
      if i.val = 0 then n - 1 else i.val - 1 := by
  by_cases h0 : i.val = 0
  · simp only [if_pos h0]
    change (i.val + n - 1) % n = n - 1
    rw [h0]
    simp [Nat.mod_eq_of_lt (show n - 1 < n by
      have := i.isLt
      omega)]
  · simp only [if_neg h0]
    change (i.val + n - 1) % n = i.val - 1
    have hArith : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [hArith]
    simp [Nat.mod_eq_of_lt (show i.val - 1 < n by omega)]

/-- For n>=4, two steps forward never equal one step backward
at the same cyclic index. -/
theorem cyclicSucc_succ_ne_pred_of_four_le
    {n : ℕ} (hn : 4 ≤ n) (t : Fin n) :
    cyclicSucc (cyclicSucc t) ≠ trainCyclicPred t := by
  intro hEq
  have hNext := cyclicSucc_val_if t
  have hNextNext := cyclicSucc_val_if (cyclicSucc t)
  have hPrev := trainCyclicPred_val_if t
  have hVal := congrArg Fin.val hEq
  rw [hNextNext, hNext, hPrev] at hVal
  split_ifs at hVal <;> omega

namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- If one ORIGINAL wagon connector contains the two distinct
consecutive vertex-boundary positions of an original long piece,
A2 forces the source BigCycle to have length three. The wagon is
then the remaining (third) connector position. -/
theorem BigCycle.old_wagon_adjacent_contacts_force_length_three
    {n : ℕ} (K : D.BigCycle n) (hn : 3 ≤ n) (hA2 : K.A2)
    (t a b : Fin n) (w : P)
    (hWagon : K.connector t = Sum.inr w)
    (ha : K.InWagonAt w a)
    (hb : K.InWagonAt w b)
    (hab : a ≠ b)
    (hAdjacent : b = cyclicSucc a) :
    n = 3 := by
  by_contra hNot3
  have hn4 : 4 ≤ n := by omega
  have hTwo : 2 ≤ n := by omega
  have hA := hA2.1 t w hWagon a ha
  have hB := hA2.1 t w hWagon b hb
  rcases hA with haPred | haSucc
  · rcases hB with hbPred | hbSucc
    · exact hab (haPred.trans hbPred.symm)
    · have hEq : t = cyclicSucc t := by
        have hh := hAdjacent
        rw [haPred, hbSucc] at hh
        rw [cyclicSucc_trainCyclicPred_of_two_le hTwo t] at hh
        exact hh.symm
      exact (cyclicSucc_ne_self_of_two_le hTwo t) hEq
  · rcases hB with hbPred | hbSucc
    · have hEq : cyclicSucc (cyclicSucc t) =
          trainCyclicPred t := by
        calc
          cyclicSucc (cyclicSucc t) = cyclicSucc a := by rw [haSucc]
          _ = b := hAdjacent.symm
          _ = trainCyclicPred t := hbPred
      exact (cyclicSucc_succ_ne_pred_of_four_le hn4 t) hEq
    · exact hab (haSucc.trans hbSucc.symm)

end OrderOneData
end StructuralRamsey.Girth
