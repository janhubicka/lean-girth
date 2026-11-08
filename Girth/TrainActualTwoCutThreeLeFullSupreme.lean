import Girth.TrainActualTwoCutTwoStandardCases
import Girth.TrainActualTwoCutCoreOwnerUnique
import Girth.TrainActualTwoCutStandardCoreShortSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: ALL EXACT two-cut selected source cycles of length at least THREE

The actual cut-indexed witness has exactly two real geometric owner
labels, which are each either a designated gluing standard or a
physical core A-edge. Thus there are exactly four label-sort cases:

* standard/standard: complete pair-edge, no-pair, mixed-bridge and
  two-wagon obstruction dispatch from two_standard_cases;
* standard/core: actual witness FullSystemGirthGT selects the
  designated standard, forces a genuine short at the isolated
  physical core occurrence, and the merged singleton source
  transfer proves ORIGINAL simultaneous supreme;
* core/standard: the exact rotated version of the preceding case;
* core/core: impossible since genuine core-edge owners are isolated,
  and at source length >=3 exactly two cyclic owner cuts permit
  at most one isolated occurrence.

No hidden local supreme assumption, no artificial B-source label
and no projection that collapses physical quotient wagon labels.
This theorem is the n>=3 residual case needed by merged Track D
output-girth closure. The original n=2 source remains open.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutThreeLeCases

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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel




/-- The genuine exactly-two-geometric-owner-cut original cycle
has full global simultaneous supremacy at every source length >=3,
from the real old-bound, witness full-system-girth and explicit
geometric physical assumptions. Nothing is assumed about the two
reduced owner sorts beyond their REAL construction. -/
theorem attachedSelectedPicture_two_cut_three_le_full_supreme
    [Finite UA]
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  let z0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let z1 : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hPred0 : trainCyclicPred z0 = z1 := by
    apply Fin.ext
    change (0 + cyclicOwnerChanges owner - 1) %
      cyclicOwnerChanges owner = 1
    rw [hTwo]
    decide
  have hPred1 : trainCyclicPred z1 = z0 := by
    apply Fin.ext
    change (1 + cyclicOwnerChanges owner - 1) %
      cyclicOwnerChanges owner = 0
    rw [hTwo]
    decide
  cases hL0 : Z.label z0 with
  | inl i =>
      cases hL1 : Z.label z1 with
      | inl j =>
          exact attachedSelectedPicture_two_cut_two_standards_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            i j hL0 hL1 hWitness hOldSupreme
      | inr b =>
          have hTarget : Z.label (trainCyclicPred z1) =
              Sum.inl i := by
            rw [hPred1]
            exact hL0
          exact attachedSelectedPicture_two_cut_standard_core_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            z1 i b hTarget hL1 hWitness hOldSupreme
  | inr b =>
      cases hL1 : Z.label z1 with
      | inl i =>
          have hTarget : Z.label (trainCyclicPred z0) =
              Sum.inl i := by
            rw [hPred0]
            exact hL1
          exact attachedSelectedPicture_two_cut_standard_core_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            z0 i b hTarget hL0 hWitness hOldSupreme
      | inr c =>
          have hOwner0 :
              owner (cyclicOwnerCutIndex owner z0) = Sum.inr b := by
            change owner (cyclicOwnerCutIndex owner z0) =
              Sum.inr b at hL0
            exact hL0
          have hOwner1 :
              owner (cyclicOwnerCutIndex owner z1) = Sum.inr c := by
            change owner (cyclicOwnerCutIndex owner z1) =
              Sum.inr c at hL1
            exact hL1
          have hSame :=
            attachedSelectedPicture_two_cut_core_owner_unique
              A hA B D C family selected e R f T U hShared μ
              K hn owner hAllowed hTwo
              (cyclicOwnerCutIndex owner z0)
              (cyclicOwnerCutIndex owner z1)
              b c hOwner0 hOwner1
          have hIndex := (cyclicOwnerCutIndex owner).injective hSame
          have hVals := congrArg Fin.val hIndex
          have hZ0 : z0.val = 0 := rfl
          have hZ1 : z1.val = 1 := rfl
          rw [hZ0, hZ1] at hVals
          omega

end ActualTwoCutThreeLeCases
end StructuralRamsey.Girth
