import Girth.TrainActualBottomTwoStandardForestTransfer
import Girth.TrainActualBottomTwoCutStandardCoreForestTransfer
import Girth.TrainActualTwoCutCoreOwnerUnique
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Complete EXACTLY-TWO-CUT bottom forest branch, source length >=3

There are four actual reduced owner pairs. Two standards use the
unique common bottom edge and checked symmetric-short source
transfer. A standard and a core edge use the checked core-singleton
short source transfer. Two core edges are impossible for a genuine
cycle of length >=3 with only two owner cuts, by the existing
core-owner uniqueness theorem.

Thus the whole two-cut original B-labelled output branch needs
only local mixed forests and old source supremacy, not full local
witness system girth. Source length two remains separate.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section BottomTwoCutAll

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

/-- All genuine exactly-two-geometric-cut original cycles of length at
least three, from a real finite mixed-forest bottom witness. Every
possible reduced owner-label sort is treated, with no ad hoc
replacement of a source B-designation by a gluing-copy label. -/
theorem attachedSelectedPicture_bottom_two_cut_all_forest_supreme
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOutputLinear : (Out).LinearPretrain)
    (H : (Wit).BottomForestGeometry)
    (q : ℕ) (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts
  let z0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let z1 : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hPred0 : trainCyclicPred z0 = z1 := by
    apply Fin.ext
    change (0 + cyclicOwnerChanges owner - 1) %
      cyclicOwnerChanges owner = 1
    rw [hTwo]
  have hPred1 : trainCyclicPred z1 = z0 := by
    apply Fin.ext
    change (1 + cyclicOwnerChanges owner - 1) %
      cyclicOwnerChanges owner = 0
    rw [hTwo]
  cases hL0 : Z.label z0 with
  | inl i =>
      cases hL1 : Z.label z1 with
      | inl j =>
          exact attachedSelectedPicture_bottom_two_standard_supreme_of_localForest
            A hA B D C family selected e R f T U hShared hRel
            hStrong hTwoCopies hOldStrong hCoreStrong hOutputLinear
            H q hLocal hOldSupreme
            K hAccept hn hOrder owner hAllowed hTwo i j hL0 hL1
      | inr b =>
          have hTarget : Z.label (trainCyclicPred z1) =
              Sum.inl i := by
            rw [hPred1]
            exact hL0
          exact attachedSelectedPicture_bottom_two_cut_standard_core_forest_supreme
            A hA B D C family selected e R f T U hShared hRel
            hStrong hTwoCopies hOldStrong hCoreStrong hOutputLinear
            H q hLocal hOldSupreme
            K hAccept hn hOrder owner hAllowed hTwo
            z1 i b hTarget hL1
  | inr b =>
      cases hL1 : Z.label z1 with
      | inl i =>
          have hTarget : Z.label (trainCyclicPred z0) =
              Sum.inl i := by
            rw [hPred0]
            exact hL1
          exact attachedSelectedPicture_bottom_two_cut_standard_core_forest_supreme
            A hA B D C family selected e R f T U hShared hRel
            hStrong hTwoCopies hOldStrong hCoreStrong hOutputLinear
            H q hLocal hOldSupreme
            K hAccept hn hOrder owner hAllowed hTwo
            z0 i b hTarget hL0
      | inr c =>
          have hOwner0 :
              owner (cyclicOwnerCutIndex owner z0) = Sum.inr b := by
            change owner (cyclicOwnerCutIndex owner z0) = Sum.inr b at hL0
            exact hL0
          have hOwner1 :
              owner (cyclicOwnerCutIndex owner z1) = Sum.inr c := by
            change owner (cyclicOwnerCutIndex owner z1) = Sum.inr c at hL1
            exact hL1
          have hSame :=
            attachedSelectedPicture_two_cut_core_owner_unique
              A hA B D C family selected e R f T U hShared μBottom
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

end BottomTwoCutAll
end StructuralRamsey.Girth
