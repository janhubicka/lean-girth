import Girth.TrainFillingContractFirstTrain
import Girth.TrainFillingInheritedParameters
import Girth.LabelledWagonCutRestriction

set_option autoImplicit false

namespace StructuralRamsey.Girth.EdgeTrainLevels

universe v
variable {E V : Type v} {m : ℕ} (T : EdgeTrainLevels E (m + 1))

theorem contractFirst_labelledCutGirth
    (edge : E → Set V) (μ : Fin (m + 1)) (g : ℕ)
    (hGirth : LabelledGirthGT (T.wagonClassCarrier edge μ.succ) g) :
    LabelledGirthGT
      (T.contractFirst.wagonClassCarrier
        (T.wagonClassCarrier edge (0 : Fin (m + 1)).succ) μ) g := by
  have hEq := funext (T.contractFirstWagonEquiv_carrier edge μ)
  rw [hEq]
  exact labelledGirthGT_of_injective_reindex
    (T.wagonClassCarrier edge μ.succ) (T.contractFirstWagonEquiv μ)
    (T.contractFirstWagonEquiv μ).injective g hGirth

theorem contractFirst_adjacentParameters
    (edge : E → Set V) (allowed : Fin (m + 1 + 1) → Set V)
    (hOld : T.AdjacentParameters edge allowed) :
    T.contractFirst.AdjacentParameters
      (T.wagonClassCarrier edge (0 : Fin (m + 1)).succ)
      (fun ν => allowed ν.succ) := by
  intro μ ν hle hAdj
  apply (T.contractFirst.parentBound_iff_representatives _ μ ν hle _).mpr
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro hNe hRel
      have hOldLe : μ.succ ≤ ν.succ := Nat.succ_le_succ hle
      have hOldAdj : ν.succ.val = μ.succ.val + 1 := by
        change ν.val + 1 = μ.val + 1 + 1
        rw [hAdj]
      have hCarrier (a : E) :
          T.contractFirst.wagonCarrier
              (T.wagonClassCarrier edge (0 : Fin (m + 1)).succ) μ (T.firstWagon a) =
            T.wagonCarrier edge μ.succ a :=
        T.contractFirstWagonEquiv_carrier edge μ (Quotient.mk _ (T.firstWagon a))
      change T.contractFirst.wagonCarrier _ μ (T.firstWagon a) ∩
        T.contractFirst.wagonCarrier _ μ (T.firstWagon b) ⊆ allowed ν.succ
      rw [hCarrier a, hCarrier b]
      exact (T.parentBound_iff_representatives edge μ.succ ν.succ hOldLe _).mp
        (hOld μ.succ ν.succ hOldLe hOldAdj) a b hNe hRel

end StructuralRamsey.Girth.EdgeTrainLevels
