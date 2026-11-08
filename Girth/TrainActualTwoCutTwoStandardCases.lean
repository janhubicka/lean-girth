import Girth.TrainActualTwoCutPairEdgeFullSupreme
import Girth.TrainActualTwoCutMixedBridgesFullSupreme
import Girth.TrainActualTwoCutSymmetricLongFullSupreme
import Girth.TrainTwoCycleMixedActualBridges
import Girth.TrainBigCycleTwoWagonObstruction
import Girth.TrainActualCutReductionDichotomy
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: all EXACT two-cut cycles with TWO designated reduced standards

Under the actual old SupremeCycleBound q and genuine lower witness
FullSystemGirthGT q, the REAL reduced cut-indexed two-standard
BigCycle has exactly two labelled gluing standards. Its connector
kind pair determines four exhaustive cases:

1. vertex/vertex with ambient pair edge: existing full original
   pair-edge short source transfer (#914);
2. vertex/vertex with no ambient pair edge: existing full original
   common-wagon fresh/old source long transfer (#929);
3. mixed vertex/wagon: physical order-one bound supplies a
   true bridge in EACH standard; the existing full mixed bridge
   source short transfer applies (#914);
4. wagon/wagon: impossible under actual witness local-piece
   bound 2, using the already merged two-wagon obstruction.

The source is a genuine acceptable selected-output BigCycle
of length at least three; the remaining n=2 original source
case is explicitly OUTSIDE this theorem. No appendix or TeX.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutTwoStandardCases

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



/-- Any actual selected attached-output source cycle of length>=3
with EXACTLY two geometric owner cuts and BOTH reduced labels
designated gluing standards has full ORIGINAL simultaneous supremacy.

The result dispatches on the two real witness connector kinds and
does not assume chosen reduced supreme plans or physical source
replacement pieces independently. -/
theorem attachedSelectedPicture_two_cut_two_standards_full_supreme
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
    (i j : I)
    (hLabel0 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label ⟨1, by omega⟩ = Sum.inl j)
    (hWitness : (Wit).FullSystemGirthGT q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hLength : n ≤ K.twiceOrder :=
    OrderOneData.BigCycle.length_le_twiceOrder Out K
  have hq : 2 ≤ q := by omega
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hStandards : ∀ k : Fin (cyclicOwnerChanges owner),
      ∃ s : I, Z.label k = Sum.inl s := by
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by
      have hb := k.isLt
      omega
    rcases hk with hZero | hOne
    · have hIndex : k =
          (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hZero
      rw [hIndex]
      exact ⟨i, hLabel0⟩
    · have hIndex : k =
          (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hOne
      rw [hIndex]
      exact ⟨j, hLabel1⟩
  have hSucc0 : cyclicSucc (⟨0, by omega⟩ :
      Fin (cyclicOwnerChanges owner)) =
      (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) := by
    apply Fin.ext
    change (0 + 1) % cyclicOwnerChanges owner = 1
    rw [hTwo]
    decide
  have hSucc1 : cyclicSucc (⟨1, by omega⟩ :
      Fin (cyclicOwnerChanges owner)) =
      (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) := by
    apply Fin.ext
    change (1 + 1) % cyclicOwnerChanges owner = 0
    rw [hTwo]
    decide
  cases hC0 : Z.connector (⟨0, by omega⟩ :
      Fin (cyclicOwnerChanges owner)) with
  | inl x =>
      cases hC1 : Z.connector (⟨1, by omega⟩ :
          Fin (cyclicOwnerChanges owner)) with
      | inl y =>
          by_cases hPair : (Wit).PairEdge x y
          · exact attachedSelectedPicture_two_cut_pairEdge_full_supreme
              A hA B D C family selected e R f T U hShared hRel μ
              hStrong hTwoCopies hOldStrong hCoreStrong
              K hAccept hLinear hn hOrder
              owner hAllowed hTwo i j hLabel0 hLabel1
              x y hC0 hC1 hPair hWitness hOldSupreme
          · exact attachedSelectedPicture_two_cut_noPair_full_supreme
              A hA B D C family selected e R f T U hShared hRel μ
              hStrong hTwoCopies hOldStrong hCoreStrong
              K hAccept hLinear hn hOrder
              owner hAllowed hTwo i j hLabel0 hLabel1
              x y hC0 hC1 hPair hWitness hOldSupreme
      | inr p =>
          have hMixed :
              (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
               Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
              (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
               Z.connector ⟨1, by omega⟩ = Sum.inl x) :=
            Or.inl ⟨hC0, hC1⟩
          have hBridges : ∀ k : Fin (cyclicOwnerChanges owner),
              (Wit).Bridge (Z.label k) x p :=
            OrderOneData.BigCycle.two_mixed_bridges_of_fullSystemGirth_of_two
              Wit hTwo Z (by omega : 1 ≤ q)
              hWitness x p hMixed
          exact attachedSelectedPicture_two_cut_mixed_bridges_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder
            owner hAllowed hTwo hStandards x p hMixed
            hBridges hOldSupreme
  | inr p =>
      cases hC1 : Z.connector (⟨1, by omega⟩ :
          Fin (cyclicOwnerChanges owner)) with
      | inl x =>
          have hMixed :
              (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
               Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
              (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
               Z.connector ⟨1, by omega⟩ = Sum.inl x) :=
            Or.inr ⟨hC0, hC1⟩
          have hBridges : ∀ k : Fin (cyclicOwnerChanges owner),
              (Wit).Bridge (Z.label k) x p :=
            OrderOneData.BigCycle.two_mixed_bridges_of_fullSystemGirth_of_two
              Wit hTwo Z (by omega : 1 ≤ q)
              hWitness x p hMixed
          exact attachedSelectedPicture_two_cut_mixed_bridges_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder
            owner hAllowed hTwo hStandards x p hMixed
            hBridges hOldSupreme
      | inr p' =>
          have hpp : p ≠ p' := by
            intro heq
            have hSame :
                Z.connector (⟨0, by omega⟩ :
                  Fin (cyclicOwnerChanges owner)) =
                Z.connector (⟨1, by omega⟩ :
                  Fin (cyclicOwnerChanges owner)) := by
              calc
                Z.connector ⟨0, by omega⟩ = Sum.inr p := hC0
                _ = Sum.inr p' := by rw [heq]
                _ = Z.connector ⟨1, by omega⟩ := hC1.symm
            have hIndex := Z.connector_injective hSame
            have hVals := congrArg Fin.val hIndex
            norm_num at hVals
          have hij : i ≠ j := by
            intro heq
            have hDiff := Z.adjacent_ne (⟨0, by omega⟩ :
              Fin (cyclicOwnerChanges owner))
            rw [hSucc0, hLabel0, hLabel1, heq] at hDiff
            exact hDiff rfl
          have hI0p : (Wit).Meets (Sum.inl i) p := by
            have h := Z.left_incident
              (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner))
            rw [hLabel0, hC0] at h
            exact h
          have hJ0p : (Wit).Meets (Sum.inl j) p := by
            have h := Z.right_incident
              (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner))
            rw [hSucc0, hLabel1, hC0] at h
            exact h
          have hJ1q : (Wit).Meets (Sum.inl j) p' := by
            have h := Z.left_incident
              (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner))
            rw [hLabel1, hC1] at h
            exact h
          have hI1q : (Wit).Meets (Sum.inl i) p' := by
            have h := Z.right_incident
              (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner))
            rw [hSucc1, hLabel0, hC1] at h
            exact h
          have hLocal : (Wit).LocalPieceSystemBound 2 := by
            intro k Z' hAcceptZ hOrderZ
            exact (Wit).localPieceSystemBound_of_supremeCycleBound
              q hWitness.2 k Z' hAcceptZ
              (hOrderZ.trans (Nat.mul_le_mul_left 2 hq))
          exact False.elim ((Wit).no_two_designated_meet_two_wagons
            hLocal i j p p' hij hpp
            hI0p hI1q hJ0p hJ1q)

end ActualTwoCutTwoStandardCases
end StructuralRamsey.Girth
