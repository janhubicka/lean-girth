import Girth.TrainActualCoreSingletonCutIndices
import Girth.TrainCyclicOwnerAbsorption
import Mathlib.Tactic

/-!
# Cyclic adjacency of canonical cut indices

If two genuine physical cuts occur at adjacent positions of a
finite cyclic owner word, they are adjacent in the canonical
Fin-indexed list of cuts as well, including the last-to-first wrap.
The positive-cut application shows that a core-owned singleton
occupies one whole indexed reduced-witness segment.

This is purely an ordering statement. It creates no replacement
edge, does not assume the old supreme bound, and uses no appendix.
-/

namespace StructuralRamsey.Girth

universe v

/-- If both the boundary just before k and the boundary at k are
actual owner changes, the indexed cut immediately preceding the
one at k is precisely the physical boundary just before k.
In particular this covers a singleton at physical position zero. -/
theorem cyclicOwnerCutIndex_pred_of_adjacent_cuts
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner) (hn : 2 ≤ n) (k : Fin n)
    (hPrevious : trainCyclicPred k ∈ cyclicOwnerCutPositions owner)
    (hCurrent : k ∈ cyclicOwnerCutPositions owner) :
    ∃ j : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner j = k ∧
      cyclicOwnerCutIndex owner (trainCyclicPred j) =
        trainCyclicPred k := by
  let f := cyclicOwnerCutIndex owner
  obtain ⟨a, ha⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner (trainCyclicPred k)).mp hPrevious
  obtain ⟨b, hb⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner k).mp hCurrent
  have hA : f a = trainCyclicPred k := ha
  have hB : f b = k := hb
  have hDifferent : trainCyclicPred k ≠ k := by
    intro hEq
    have hh := cyclicSucc_trainCyclicPred_of_two_le hn k
    rw [hEq] at hh
    exact (cyclicSucc_ne_self_of_two_le hn k) hh
  have hab : a ≠ b := by
    intro hEq
    apply hDifferent
    calc
      trainCyclicPred k = f a := hA.symm
      _ = f b := congrArg f hEq
      _ = k := hB
  have hc : 2 ≤ cyclicOwnerChanges owner := by
    have hneq : a.val ≠ b.val := by
      intro h
      exact hab (Fin.ext h)
    have haBound := a.isLt
    have hbBound := b.isLt
    omega
  have hNext : cyclicSucc a = b := by
    by_cases hk0 : k.val = 0
    · have hp : (trainCyclicPred k).val = n - 1 := by
        change (k.val + n - 1) % n = n - 1
        rw [hk0]
        simp only [zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      have haLastVal : (f a).val = n - 1 := by
        rw [hA]
        exact hp
      have hbFirstVal : (f b).val = 0 := by
        rw [hB]
        exact hk0
      have hBZero : b.val = 0 := by
        by_contra hNot
        have hbPositive : 0 < b.val := by omega
        let first : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
        have hLess : first < b := by
          change 0 < b.val
          exact hbPositive
        have hOutLess : (f first).val < (f b).val :=
          f.strictMono hLess
        omega
      have hALast : a.val + 1 = cyclicOwnerChanges owner := by
        by_contra hNot
        have hSmall : a.val + 1 < cyclicOwnerChanges owner := by
          have := a.isLt
          omega
        let last : Fin (cyclicOwnerChanges owner) :=
          ⟨cyclicOwnerChanges owner - 1, by omega⟩
        have hLess : a < last := by
          change a.val < cyclicOwnerChanges owner - 1
          omega
        have hOutLess : (f a).val < (f last).val :=
          f.strictMono hLess
        have hLastBound := (f last).isLt
        omega
      apply Fin.ext
      change (a.val + 1) % cyclicOwnerChanges owner = b.val
      rw [hALast, Nat.mod_self]
      exact hBZero.symm
    · have hkPositive : 0 < k.val := by omega
      have hp : (trainCyclicPred k).val = k.val - 1 := by
        change (k.val + n - 1) % n = k.val - 1
        have hArith : k.val + n - 1 = n + (k.val - 1) := by omega
        rw [hArith]
        simp [Nat.mod_eq_of_lt (show k.val - 1 < n by omega)]
      have hOutAdjacent : (f a).val + 1 = (f b).val := by
        rw [hA, hB]
        omega
      have hAB : a < b := by
        by_contra hNot
        have hBA : b ≤ a := le_of_not_gt hNot
        have hReverse : (f b).val ≤ (f a).val :=
          f.monotone hBA
        omega
      have hNoIntermediate : b.val = a.val + 1 := by
        by_contra hNot
        have hGap : a.val + 1 < b.val := by
          have hLess : a.val < b.val := hAB
          omega
        let mid : Fin (cyclicOwnerChanges owner) :=
          ⟨a.val + 1, by have := b.isLt; omega⟩
        have hAmid : a < mid := by
          change a.val < a.val + 1
          omega
        have hMidb : mid < b := by
          change a.val + 1 < b.val
          exact hGap
        have hLower : (f a).val < (f mid).val :=
          f.strictMono hAmid
        have hUpper : (f mid).val < (f b).val :=
          f.strictMono hMidb
        omega
      apply Fin.ext
      change (a.val + 1) % cyclicOwnerChanges owner = b.val
      rw [Nat.mod_eq_of_lt (by have := b.isLt; omega)]
      exact hNoIntermediate.symm
  have hPred : trainCyclicPred b = a := by
    rw [← hNext]
    exact trainCyclicPred_cyclicSucc_of_two_le hc a
  exact ⟨b, hB, by rw [hPred]; exact hA⟩

open StructuralRamsey.RelStructure

universe u w
section ActualCoreSingleton

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type w}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- The two actual boundary cuts around a core-owned singleton are
cyclically consecutive in the canonical reduced witness. The
predecessor-index equality, including wrap, is derived rather than
assumed by later physical short-piece transport. -/
theorem attachedSelectedPicture_core_singleton_consecutive_cut_indices
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge) (hCore : owner k = Sum.inr b) :
    ∃ j : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner j = k ∧
      cyclicOwnerCutIndex owner (trainCyclicPred j) =
        trainCyclicPred k := by
  obtain ⟨jPrev, jNow, hPrev, hNow⟩ :=
    attachedSelectedPicture_core_singleton_two_cut_indices
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed k b hCore
  apply cyclicOwnerCutIndex_pred_of_adjacent_cuts
    owner K.length_ge_two k
  · exact (cyclicOwnerCutIndex_mem_iff owner _).mpr ⟨jPrev, hPrev⟩
  · exact (cyclicOwnerCutIndex_mem_iff owner _).mpr ⟨jNow, hNow⟩

end ActualCoreSingleton
end StructuralRamsey.Girth
