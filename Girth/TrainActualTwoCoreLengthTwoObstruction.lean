import Girth.TrainRecursiveInitialTailSystem
import Girth.TrainSystemCutGirthTwo
import Girth.TrainSelectedCycleGeometricOwners
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# No acceptable two-occurrence edge-only cycle in a linear pretrain

Physical edge linearity and physical wagon linearity alone exclude an
acceptable edge-only BigCycle on exactly two occurrences. The result is
not an application of output FullSystemGirthGT (which would be circular):
the previously checked edge-only exclusion theorem requires only the
LABELLED two-cut girth bound, and this follows already from pairwise
linearity of wagon carriers.

This closes the special n=2 source branch when BOTH geometric owners
are genuine core physical edges: geometric core ownership forces the
corresponding output label to be the very same physical edge. No
hypothesis about the witness supreme-cycle bound, an artificial
designated source label or new physical support edges is inserted.

The general n>=3 owner classification and remaining standard-containing
two-cut physical transfers are separate Path A obligations. This file
does not claim FullSystemGirthGT of the attached output or finish the
recursive witness construction. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

namespace OrderOneData

universe v
variable {V E I P : Type v}

/-- Under physical pretrain linearity, an acceptable two-occurrence
big cycle cannot have only edge labels. In particular no output
FullSystemGirthGT or supreme bound is assumed. -/
theorem BigCycle.no_edge_only_two_of_linear
    (D : OrderOneData V E I P)
    (hLinear : D.LinearPretrain)
    (K : D.BigCycle 2)
    (hAccept : K.Acceptable)
    (hOnly : ∀ j : Fin 2, ∃ b : E, K.label j = Sum.inr b) :
    False := by
  have hOrder : K.twiceOrder ≤ 2 * 2 := by
    unfold OrderOneData.BigCycle.twiceOrder
    rw [Fin.sum_univ_two]
    have h0 := twiceOccurrenceWeight_le_two
      (connectorKind (K.connector (0 : Fin 2)))
      (connectorKind (K.connector (cyclicSucc (0 : Fin 2))))
    have h1 := twiceOccurrenceWeight_le_two
      (connectorKind (K.connector (1 : Fin 2)))
      (connectorKind (K.connector (cyclicSucc (1 : Fin 2))))
    omega
  have hCut :
      LabelledGirthGT (fun p : P => {x : V | D.WagonVertex p x}) 2 :=
    labelledGirthGT_two_of_pairwiseSubsingleton _
      (fun p r hpr => hLinear.2 p r hpr)
  choose edge hLabel using hOnly
  exact K.false_of_edge_only_of_labelledCutGirth
    edge hLabel hLinear.1 hAccept 2 (by decide) hCut hOrder

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualTwoCoreLengthTwo

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  (actualAPictureEdgeEquiv A hA C.toRelStructure S R f)
    (physicalCoreEdge
      (sharedOldACarrierInclusion A C.toRelStructure S) I b))

/-- At source length two, a genuine acceptable output cycle with
linear physical pretrain cannot assign BOTH occurrence carriers to
physical core-edge owners. No separate system-girth premise is used. -/
theorem attachedSelectedPicture_two_core_owners_length_two_false
    (hLinear : (Out).LinearPretrain)
    (K : (Out).BigCycle 2)
    (hAccept : K.Acceptable)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hAllCore : ∀ j : Fin 2, ∃ b : CoreEdge,
      owner j = Sum.inr b) : False := by
  apply OrderOneData.BigCycle.no_edge_only_two_of_linear
    (Out) hLinear K hAccept
  intro j
  obtain ⟨b, hb⟩ := hAllCore j
  have h := hAllowed j
  rw [hb] at h
  change K.label j = Sum.inr (CoreActual b) at h
  exact ⟨CoreActual b, h⟩

end ActualTwoCoreLengthTwo

end StructuralRamsey.Girth
