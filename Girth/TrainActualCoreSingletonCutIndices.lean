import Girth.TrainSelectedCycleGeometricOwners
import Girth.TrainCyclicCutIndices

/-!
# Actual core singleton positions yield two indexed cyclic cuts

A genuine core-edge singleton cannot have the same geometric owner as
either neighbor. Therefore both original boundaries are genuine cuts
and appear in the verified canonical finite cut enumeration, including
cyclic wrap. Identifying the two ENUMERATION indices as consecutive is
a further (purely combinatorial) statement, not assumed here.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualCoreSingletonCutIndices

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
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

/-- Both physical boundaries of a core-owned singleton occur in the
canonical indexed cyclic cut list. This constructs the two cut indices
from actual cycle geometry instead of postulating their existence. -/
theorem attachedSelectedPicture_core_singleton_two_cut_indices
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n) (b : CoreEdge)
    (hCore : owner k = Sum.inr b) :
    ∃ jPrev jNow : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner jPrev = trainCyclicPred k ∧
      cyclicOwnerCutIndex owner jNow = k := by
  obtain ⟨hBefore, hAfter⟩ :=
    attachedSelectedPicture_geometric_core_owner_isolated
      A hA B D C family selected e R f T U hShared μ
      K owner hAllowed k b hCore
  have hLeftChange :
      owner (trainCyclicPred k) ≠
        owner (cyclicSucc (trainCyclicPred k)) := by
    rw [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two k]
    rw [hCore]
    exact hBefore
  have hRightChange : owner k ≠ owner (cyclicSucc k) := by
    rw [hCore]
    intro h
    exact hAfter h.symm
  have hLeftCut :
      trainCyclicPred k ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner _).mpr hLeftChange
  have hRightCut : k ∈ cyclicOwnerCutPositions owner :=
    (mem_cyclicOwnerCutPositions_iff owner _).mpr hRightChange
  obtain ⟨jPrev, hjPrev⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner (trainCyclicPred k)).mp hLeftCut
  obtain ⟨jNow, hjNow⟩ :=
    (cyclicOwnerCutIndex_mem_iff owner k).mp hRightCut
  exact ⟨jPrev, jNow, hjPrev, hjNow⟩

end ActualCoreSingletonCutIndices
end StructuralRamsey.Girth
