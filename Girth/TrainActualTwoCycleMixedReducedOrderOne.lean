import Girth.TrainActualCutIndexedBigCycle
import Girth.TrainBigCycleOrderBudget
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# An actual original two-cycle with mixed connector kinds reduces to order one

An original selected-output BigCycle of length TWO with two
distinct geometric owner cuts has a literal length-two lower
witness BigCycle, with TRUE cut-index connector geometry.
The known restriction theorem transfers the A2/A3 source
geometry and never increases twice the numerical order.

If the two original connectors have DIFFERENT kinds, each
source occurrence has twice-weight one, so the original
numerical twice-order is exactly two. Every occurrence of
the genuine witness BigCycle has twice-weight at least one,
hence the reduced word has twice-order at least two.
The source restriction inequality therefore forces the
reduced numerical order to be exactly ONE.

No reduced A1/Acceptable assumption is smuggled in.
In particular, the result applies when one reduced label is a
physical core edge. It provides the missing numeric hypothesis
for the checked order-one witness bridge extraction, leaving
the original source B-copy ownership/parent transport separate.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualN2MixedReducedOrder

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- The genuine indexed geometric reduction of an ORIGINAL
two-occurrence source with exactly two cuts and MIXED original
connector kinds has twiceOrder=2, so its numerical order is one.
No witness A1 or source-to-witness label identification is used. -/
theorem attachedSelectedPicture_two_cycle_mixed_reduced_order_one
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hMixed : connectorKind (K.connector (0 : Fin 2)) ≠
      connectorKind (K.connector (1 : Fin 2))) :
    (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)).twiceOrder = 2 := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hOriginalOrder : K.twiceOrder = 2 := by
    simp [OrderOneData.BigCycle.twiceOrder, Fin.sum_univ_two,
      cyclicSucc, twiceOccurrenceWeight, hMixed, hMixed.symm]
  have hTransfer :
      cyclicOwnerChanges owner ≤ 2 ∧
      Z.twiceOrder ≤ K.twiceOrder ∧ Z.A2 ∧ Z.A3 := by
    exact attachedSelectedPicture_geometric_cut_restriction_bounds
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega) hAccept.2.1 hAccept.2.2
  have hLower : cyclicOwnerChanges owner ≤ Z.twiceOrder :=
    Z.length_le_twiceOrder
  omega

end ActualN2MixedReducedOrder
end StructuralRamsey.Girth
