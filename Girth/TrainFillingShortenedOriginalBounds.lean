import Girth.TrainFillingContractFirstBounds
import Girth.TrainFillingIndexedActualMPhysicalTrain
import Girth.TrainFillingIndexedContractedTrainGirth

set_option autoImplicit false

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {A E V X C : Type v} {m : ℕ} [Nontrivial X]
variable (T : EdgeTrainLevels E (m + 1)) (hm : 0 < m)
variable (edge : E → Set V) (W : C → PrivateWagonInput V T.FirstWagon X)
variable (hCarrier : ∀ c : C, (W c).oldCarrier =
  T.wagonClassCarrier edge (0 : Fin (m + 1)).succ)
variable (A₀ : RelStructure L A) (M : RelStructure L (Vertex W))
variable (hSupport : supportCopies A₀ M = Set.range (contractedCarrier W))
variable (hLinear : ∀ c : C, ∀ p q : T.FirstWagon, p ≠ q →
  ((W c).oldCarrier p ∩ (W c).oldCarrier q).Subsingleton)

local notation "Short" =>
  contractedPhysicalTrain W A₀ M (EdgeTrainLevels.contractFirst T) hm hSupport hLinear

include hCarrier in
/-- A literal cut of the actual relational shortened train inherits its
bound from the corresponding positive cut of the original train. -/
theorem shortenedOriginal_labelledCutGirth
    (μ : Fin (m + 1)) (g : ℕ)
    (hGirth : LabelledGirthGT (T.wagonClassCarrier edge μ.succ) g) :
    LabelledGirthGT ((Short).wagonClassCarrier (fun e => e.1) μ) g := by
  apply contractedPhysicalTrain_labelledCutGirth W A₀ M T.contractFirst hm
    hSupport hLinear μ g
  apply contractedChoiceTrain_labelledCutGirth_allLevels W T.contractFirst hm μ g
  intro c
  rw [hCarrier c]
  exact T.contractFirst_labelledCutGirth edge μ g hGirth

include hCarrier in
/-- All adjacent parameters of the actual relational shortened train
follow from the original positive parameters, enlarged by membership
in the corresponding original unary part predicates. -/
theorem shortenedOriginal_adjacentParameters
    (allowed : Fin (m + 1 + 1) → Set V) (shortAllowed : Fin (m + 1) → Set (Vertex W))
    (hOld : T.AdjacentParameters edge allowed)
    (hAllowed : ∀ ν c x, x ∈ allowed ν.succ → tagVertex W c (Sum.inl x) ∈ shortAllowed ν) :
    (Short).AdjacentParameters (fun e => e.1) shortAllowed := by
  apply contractedPhysicalTrain_adjacentParameters W A₀ M T.contractFirst hm
    hSupport hLinear shortAllowed
  have hRaw := contractedChoiceTrain_adjacentParameters W T.contractFirst hm
    (fun ν => allowed ν.succ) (by
      intro c
      rw [hCarrier c]
      exact T.contractFirst_adjacentParameters edge allowed hOld)
  intro μ ν hle hAdj a b hNe hParent z hz
  have hIn := hRaw μ ν hle hAdj hNe hParent hz
  rcases z with ⟨c, z⟩
  obtain ⟨x, hx, heq⟩ := hIn
  change Sum.inl x = z at heq
  change (⟨c, z⟩ : Vertex W) ∈ shortAllowed ν
  rw [← heq]
  exact hAllowed ν c x hx

end StructuralRamsey.Girth.IndexedPrivateChoice
