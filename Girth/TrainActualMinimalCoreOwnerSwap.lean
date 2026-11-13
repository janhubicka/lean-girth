import Girth.TrainMinimalOwnerReassignment
import Girth.TrainSelectedCycleGeometricOwners

/-!
# Minimum geometric owners: the actual core-edge singleton obstruction

If a real core-edge owner sits between two owner changes, it cannot
have an adjacent standard owner that contains the physical edge:
that standard would be an admissible new owner and lower the cut count.

This closes the MINIMALITY step only.  Proving that an arbitrary
short-normalized bottom mixed singleton supplies such a containing
standard is the still-open physical incidence/normalization interface.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualMinimalCoreOwnerSwap

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

/-- A minimum geometric assignment cannot have a core-edge singleton
beside a standard owner carrying its whole physical edge. Both adjacent
directions are covered, as is the cyclic closing position. -/
theorem attachedSelectedPicture_minimal_no_adjacent_containing_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ k, GeomAllowed (K.label k) (other k)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n) (b : CoreEdge) (i : I)
    (hCore : owner k = Sum.inr b)
    (hAdjacent : owner (trainCyclicPred k) = Sum.inl i ∨
      owner (cyclicSucc k) = Sum.inl i)
    (hContained : (Out).carrier (K.label k) ⊆ copyCarrier (Std i)) : False := by
  have hIsolated := attachedSelectedPicture_geometric_core_owner_isolated
    A hA B D C family selected e R f T U hShared μ
    K owner hAllowed k b hCore
  have hLeft : owner (trainCyclicPred k) ≠ owner k := by
    rw [hCore]
    exact hIsolated.1
  have hRight : owner k ≠ owner (cyclicSucc k) := by
    rw [hCore]
    exact hIsolated.2.symm
  have hReassignment :
      GeomAllowed (K.label k) (Sum.inl i : I ⊕ CoreEdge) := by
    exact hContained
  have hNeighbour :
      (Sum.inl i : I ⊕ CoreEdge) = owner (trainCyclicPred k) ∨
        (Sum.inl i : I ⊕ CoreEdge) = owner (cyclicSucc k) := by
    rcases hAdjacent with hp | hs
    · exact Or.inl hp.symm
    · exact Or.inr hs.symm
  exact minimalCyclicOwner_no_isolated_adjacent_reassignment
    K.length_ge_two
    (fun j a => GeomAllowed (K.label j) a)
    owner hAllowed hMinimal k hLeft hRight
    (Sum.inl i) hReassignment hNeighbour

end ActualMinimalCoreOwnerSwap
end StructuralRamsey.Girth
