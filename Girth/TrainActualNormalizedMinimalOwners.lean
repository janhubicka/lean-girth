import Girth.TrainFillingMixedNormalization
import Girth.TrainSelectedCycleGeometricOwners

/-!
# Normalize before minimizing geometric owners of the actual output cycle

Reuse the previously checked simultaneous short normalization, preserving
the entire connector word, length, order and genuine supreme-label pullback.
Only after normalization choose a minimum of all admissible GEOMETRIC owner
assignments. No original target label is replaced by a reduced witness copy.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualNormalizationAndMinimum

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

/-- Normalize any length-at-least-three acceptable attached output cycle,
then minimize its genuine geometric owners. A later original selected-copy
supreme plan pulls back without changing its designated label. -/
theorem attachedSelectedPicture_exists_normalized_minimal_geometric_owners
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) :
    ∃ Z : (Out).BigCycle n,
      Z.Acceptable ∧ Z.twiceOrder = K.twiceOrder ∧
      Z.MixedNormalized Out ∧
      (∀ j : Fin n, Z.connector j = K.connector j) ∧
      (∃ owner : Fin n → I ⊕ CoreEdge,
        (∀ j, GeomAllowed (Z.label j) (owner j)) ∧
        (∀ other : Fin n → I ⊕ CoreEdge,
          (∀ j, GeomAllowed (Z.label j) (other j)) →
          cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)) ∧
      (∀ kZ : Fin n, Z.HasSupremeAt Out kZ →
        ∃ kK : Fin n, K.label kK = Z.label kZ ∧
          K.HasSupremeAt Out kK) := by
  obtain ⟨Z, hConnectors, hZAccept, hOrder, hNormalized, hPullback⟩ :=
    K.exists_mixed_normalized Out hAccept hLinear hn
  obtain ⟨owner, hAllowed, hMinimum⟩ :=
    attachedSelectedPicture_cycle_exists_minimal_geometric_owners
      A hA B D C family selected e R f T U hShared μ Z
  exact ⟨Z, hZAccept, hOrder, hNormalized, hConnectors,
    ⟨owner, hAllowed, hMinimum⟩, hPullback⟩

end ActualNormalizationAndMinimum
end StructuralRamsey.Girth
