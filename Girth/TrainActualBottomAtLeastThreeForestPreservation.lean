import Girth.TrainActualBottomThreeCutForestTransfer
import Girth.TrainActualBottomTwoCutAllForestTransfer
import Girth.TrainActualZeroCutGlobalSupreme
import Girth.TrainNoSingleCyclicOwnerCut
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Bottom-forest output preservation for EVERY original source n >= 3

Start with the ACTUAL output cycle. Simultaneous short-normalization
preserves its connectors/order and pulls eventual ORIGINAL labelled
supreme plans back. Minimize real geometric owners. A direct cyclic
charging argument bounds cuts by original order, without segment
blocks. The remaining cut count is 0, 2 or >=3:

  0: checked one-standard pullback and old original supreme bound;
  2: genuine local forest gives the common bottom edge and short
     standard/standard or standard/core transfer, core/core excluded;
 >=3: real reduced witness globally supreme from bottom local
     forest, then the checked original one-pass physical transfer.

This is a conditional ONE-LEVEL theorem with the genuine local
forest witness, original source bounds and literal gluing geometry.
It does not construct the finite forest witness or assert output
supremeness at ORIGINAL source length two.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section BottomAtLeastThree

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

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μBottom
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "Wit" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

include hRel

/-- Complete bottom one-step ORIGINAL B-labelled supreme-cycle bound
for source length n >= 3, under the actual selected local forest
through q and old original supreme-cycle bound. The length-two output
case is deliberately outside this theorem. -/
theorem attachedSelectedPicture_bottom_supreme_three_le_of_localForest
    [Finite UA] [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (H : (Wit).BottomForestGeometry)
    (q : ℕ)
    (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q) :
    K.HasSimultaneousSupreme := by
  let HOut := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hPhysical
  have hOutputLinear : (Out).LinearPretrain :=
    OrderOneData.BottomForestGeometry.linearPretrain Out HOut
  obtain ⟨Z, hZAccept, hZOrder, _hNormalized, _hConnectors,
    owner, hAllowed, _hMinimal, hBudget, hPull⟩ :=
    attachedSelectedPicture_bottom_exists_normalized_minimum_cut_budget
      A hA B D C family selected e R f T U hShared hRel
      hPhysical (fun b => hStrong b.1.base b.1.base_mem)
      K hAccept hn hOrder
  have hZOrderBound : Z.twiceOrder ≤ 2 * q := by
    rw [hZOrder]
    exact hOrder
  have hZSupreme : Z.HasSimultaneousSupreme := by
    rcases cyclicOwnerChanges_zero_or_two_le Z.length_ge_two owner with
      hZero | hPositive
    · exact attachedSelectedPicture_zero_cut_supreme_of_old_bound
        A hA B D C family selected e R f T U hShared hRel μBottom
        hStrong hTwoCopies hOldStrong hCoreStrong
        Z hZAccept hOldSupreme hZOrderBound
        owner hAllowed hZero
    · by_cases hTwo : cyclicOwnerChanges owner = 2
      · exact attachedSelectedPicture_bottom_two_cut_all_forest_supreme
          A hA B D C family selected e R f T U hShared hRel
          hStrong hTwoCopies hOldStrong hCoreStrong hOutputLinear
          H q hLocal hOldSupreme
          Z hZAccept hn hZOrderBound owner hAllowed hTwo
      · have hThree : 3 ≤ cyclicOwnerChanges owner := by omega
        exact attachedSelectedPicture_bottom_three_cut_supreme_of_localForest
          A hA B D C family selected e R f T U hShared hRel
          hStrong hTwoCopies hOldStrong hCoreStrong hOutputLinear
          H q hLocal hOldSupreme
          Z hZAccept hn hZOrderBound owner hAllowed hThree hBudget
  obtain ⟨kZ, hDesignated, pieces, hPlan, hGlobal⟩ := hZSupreme
  obtain ⟨kK, _hSameLabel, hSupreme⟩ :=
    hPull kZ ⟨hDesignated, pieces, hPlan, hGlobal⟩
  exact K.hasSimultaneousSupreme_of_hasSupremeAt Out kK hSupreme

end BottomAtLeastThree
end StructuralRamsey.Girth
