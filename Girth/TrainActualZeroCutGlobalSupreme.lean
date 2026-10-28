import Girth.TrainActualStandardPhysicalMap
import Girth.TrainActualZeroCutAcceptable

/-!
# Genuine zero-cut simultaneous supreme plans lift to the output

The original circulation one-standard argument requires more than
an acceptable old witness cycle. The OLD source system supplies a
globally legal simultaneous supreme replacement plan, and the
attached output must inherit an ACTUAL globally legal replacement
word, preserving the same chosen designated occurrence.

The preceding verified components identify every zero-cut output
cycle with a legal acceptable old BigCycle with exactly corresponding
labels and connectors. The genuine standard four-sort incidence map
preserves and reflects the physical data necessary to transport the
FULL supreme plan, including its PlanProducesBigCycle witness.

This module assembles that conclusion under explicit:
* nontrivial (at least two old A-support edges) A-strong B-targets;
* exact shared train preservation/reflection and nonempty shared support;
* A-strong old gluing subsystem AND every A-strong core gluing image;
* the usual source SupremeCycleBound at the same numerical cutoff.

The conclusion is the actual output HasSimultaneousSupreme; this
proves the ZERO-CUT one-standard supreme branch. Positive-cut global
preservation, full picture-step hypothesis derivation and the
circulation induction remain separate. No appendix.
-/

namespace StructuralRamsey.Girth
namespace OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- BigCycles are identified by their literal label and connector
functions. All the other structure fields are proof-irrelevant. -/
theorem BigCycle.eq_of_label_connector {n : ℕ}
    (C K : D.BigCycle n)
    (hLabels : ∀ j : Fin n, C.label j = K.label j)
    (hConnectors : ∀ j : Fin n, C.connector j = K.connector j) :
    C = K := by
  have hl : C.label = K.label := funext hLabels
  have hc : C.connector = K.connector := funext hConnectors
  cases C
  cases K
  cases hl
  cases hc
  rfl

end OrderOneData

open StructuralRamsey.RelStructure

universe u v
section ActualZeroCutGlobalSupreme

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
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A faithful old BigCycle and a literal physical map give the same
OUTPUT BigCycle at the exact selected labels/connector positions.
Not merely isomorphic carriers: equality of the STRUCTURES is used
to transport full HasSimultaneousSupreme. -/
theorem attachedSelectedPicture_standard_mappedBigCycle_eq
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (i : I) {n : ℕ}
    (Z : (Old).BigCycle n) (K : (Out).BigCycle n)
    (hLabels : ∀ j : Fin n,
      LabelMap i (Z.label j) = K.label j)
    (hConnectors : ∀ j : Fin n,
      Sum.map (Std i) (StdWagon i) (Z.connector j) =
        K.connector j) :
    (attachedSelectedPicture_standard_physicalMap
      A hA B D C family selected e R f T U hShared hRel μ
      hOldStrong hCoreStrong i).mapBigCycle Z = K := by
  let M := attachedSelectedPicture_standard_physicalMap
    A hA B D C family selected e R f T U hShared hRel μ
    hOldStrong hCoreStrong i
  -- The physical label map and the paper's tagged-label map are
  -- propositionally equal only after splitting the sum constructor.
  have hMapLabel (a : Selected ⊕ OldEdge) :
      M.mapLabel a = LabelMap i a := by
    cases a <;> rfl
  have hMapConnector (z : X ⊕ (T.wagonSetoid μ).Quotient) :
      M.mapConnector z = Sum.map (Std i) (StdWagon i) z := by
    cases z <;> rfl
  apply OrderOneData.BigCycle.eq_of_label_connector (Out)
    (M.mapBigCycle Z) K
  · intro j
    change M.mapLabel (Z.label j) = K.label j
    rw [hMapLabel]
    exact hLabels j
  · intro j
    change M.mapConnector (Z.connector j) = K.connector j
    rw [hMapConnector]
    exact hConnectors j

/-- The actual ZERO-CUT output cycle inherits a fully GLOBAL
simultaneous supreme plan, not merely short and long pieces.
The selected target identity is preserved literally; source and
output twice-orders agree, so the old cutoff is applied with no
extra numerical slack. -/
theorem attachedSelectedPicture_zero_cut_supreme_of_old_bound [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (hOldSupreme : (Old).SupremeCycleBound q)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j : Fin n, GeomAllowed (K.label j) (owner j))
    (hZero : cyclicOwnerChanges owner = 0) :
    K.HasSimultaneousSupreme := by
  obtain ⟨i, Z, hLabels, hConnectors, hAcceptOld, hSameOrder⟩ :=
    attachedSelectedPicture_zero_cut_acceptable_oldBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwo K hAccept owner hAllowed hZero
  let M := attachedSelectedPicture_standard_physicalMap
    A hA B D C family selected e R f T U hShared hRel μ
    hOldStrong hCoreStrong i
  have hOldOrder : Z.twiceOrder ≤ 2 * q := by
    rw [hSameOrder]
    exact hOrder
  have hOldGlobal : Z.HasSimultaneousSupreme :=
    hOldSupreme n Z hAcceptOld hOldOrder
  have hOutputGlobal : (M.mapBigCycle Z).HasSimultaneousSupreme :=
    M.hasSimultaneousSupreme_map Z hOldGlobal
  have hCycleEq : M.mapBigCycle Z = K :=
    attachedSelectedPicture_standard_mappedBigCycle_eq
      A hA B D C family selected e R f T U hShared hRel μ
      hOldStrong hCoreStrong i Z K hLabels hConnectors
  rw [← hCycleEq]
  exact hOutputGlobal

end ActualZeroCutGlobalSupreme
end StructuralRamsey.Girth
