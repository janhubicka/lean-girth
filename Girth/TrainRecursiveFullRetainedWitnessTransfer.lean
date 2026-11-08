import Girth.TrainRecursiveFineWitnessSystemGirth
import Girth.TrainRecursiveSelectedGluingIncidence

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact retained full-system girth without lowering the cutoff to two

The checked interior-full transport after forgetting first refinement
cuts lowers all fine FullSystemGirthGT certificates to the cutoff 2.
That suffices for linearity and A-strongness, but not for the requested
original positive tail SupremeCycleBound at possibly larger thresholds.

This theorem transports the WHOLE labelled gluing incidence record
with the original, index-dependent cutoff unchanged. A fine-stage
FullSystemGirthGT at the retained firstForgetIndex of an old cut
becomes the FullSystemGirthGT of the actual forgotten shared witness
at the same old cut. No new cycle proof, high girth, or synthetic
physical edge family is assumed. The only input is genuine fine
FullSystemGirthGT at exactly those shifted coordinates.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- Forgetting initial refinement levels preserves full system girth
at every retained positive *old* cut with its exact original cutoff
value, including all simultaneous supreme plans. The physical
gluing incidence record and the actual shared-witness record are
equal after the checked forgetFirstCuts coordinate reindexing. -/
theorem activeGluingWitness_retainedFull_exact
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P)
    (R : RelStructure L Y)
    (f : I → Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A R) (m + d))
    (hm : 0 < m)
    (g : Fin (m + 1) → ℕ)
    (hFine : ∀ μ : Fin (m + 1),
      0 < μ.val → μ.val < m →
      (activeGluingWitnessOrderOneData A C α R f T
        (EdgeTrainLevels.firstForgetIndex m d μ)).FullSystemGirthGT
          (g μ)) :
    ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (sharedWitnessOrderOneData (T.forgetFirstCuts hm) μ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          (activeCarrier A C α) R f)
        (Subtype.val : OldACarrierEdge A R → Set Y)).FullSystemGirthGT
          (g μ) := by
  intro μ hPos hLt
  have hCoarse :
      (activeGluingWitnessOrderOneData A C α R f
        (T.forgetFirstCuts hm) μ).FullSystemGirthGT (g μ) := by
    rw [activeGluingWitness_forgetFirstCuts_eq
      A C α R f T hm μ]
    exact hFine μ hPos hLt
  rw [activeGluingWitnessOrderOneData_eq_shared
    A C α R f (T.forgetFirstCuts hm) μ] at hCoarse
  exact hCoarse

end StructuralRamsey.Girth
