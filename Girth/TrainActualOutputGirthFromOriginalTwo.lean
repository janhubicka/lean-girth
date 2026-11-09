import Girth.TrainActualOriginalTwoCycleSupreme
import Girth.TrainActualTwoCutThreeLeFullSupreme
import Girth.TrainActualZeroCutGlobalSupreme
import Girth.TrainNoSingleCyclicOwnerCut
import Girth.TrainActualSimultaneousSegmentTransfer

set_option autoImplicit false
set_option Elab.async false

/-! Actual output full system girth with arbitrary geometric owners.
The three-or-more-cut branch uses one simultaneous segment transfer. There
is no minimizing owner choice and no residual source length-two callback. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualOutputGirthFromOriginalTwo

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

/-- Full selected attached-output system girth with no unresolved
source length-two or two-cut callback. All remaining inputs are geometric
hypotheses and the ordinary old/witness induction hypotheses. -/
theorem attachedSelectedPicture_fullSystemGirth
    [Finite UA]
    (q : ℕ) (hq : 1 ≤ q)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    (hWitness : (Wit).FullSystemGirthGT q) :
    (Out).FullSystemGirthGT q := by
  classical
  refine ⟨hLinear, ?_⟩
  intro n K hAccept hOrder
  have hExists (k : Fin n) : ∃ own : I ⊕ CoreEdge,
      GeomAllowed (K.label k) own := by
    rcases attachedSelectedPicture_cycle_every_label_has_source
        A hA B D C family selected e R f T U hShared μ K k with
      ⟨i, old, hLabel⟩ | ⟨b, hLabel⟩
    · exact ⟨.inl i, selectedOutput_literal_owner_geometric
        A hA B D C family selected e R f T U hShared μ
        (K.label k) (.inl i) ⟨old, hLabel⟩⟩
    · exact ⟨.inr b, hLabel⟩
  choose owner hAllowed using hExists
  rcases cyclicOwnerChanges_zero_or_two_le K.length_ge_two owner with hZero | hPositive
  · exact attachedSelectedPicture_zero_cut_supreme_of_old_bound
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hOldSupreme hOrder owner hAllowed hZero
  · by_cases hTwo : cyclicOwnerChanges owner = 2
    · by_cases hn : n = 2
      · subst n
        exact attachedSelectedPicture_original_two_cycle_supreme
          A hA B D C family selected e R f T U hShared hRel μ
          q hq hStrong hTwoCopies hOldSupreme hWitness
          K hAccept hLinear owner hAllowed hTwo hOrder
      · have hn3 : 3 ≤ n := by have := K.length_ge_two; omega
        exact attachedSelectedPicture_two_cut_three_le_full_supreme
          A hA B D C family selected e R f T U hShared hRel μ
          hStrong hTwoCopies hOldStrong hCoreStrong
          K hAccept hLinear hn3 hOrder owner hAllowed hTwo hWitness hOldSupreme
    · exact attachedSelectedPicture_three_cut_simultaneous_segment_transfer
        A hA B D C family selected e R f T U hShared hRel μ
        hStrong hTwoCopies hOldStrong hCoreStrong
        K hAccept hLinear hOrder owner hAllowed (by omega) hq hWitness hOldSupreme

end ActualOutputGirthFromOriginalTwo
end StructuralRamsey.Girth
