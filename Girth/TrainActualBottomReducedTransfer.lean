import Girth.TrainBottomReducedSupremePieces
import Girth.TrainActualTwoCutPairEdgeGeometricSupreme
import Girth.TrainActualTwoCutStandardCoreReducedSupreme
import Girth.TrainActualTwoCutMixedBridgesFullSupreme
import Girth.TrainActualTwoCutCoreOwnerUnique
import Girth.TrainActualThreeCutOnePassSupreme
import Girth.TrainActualOriginalTwoCycleSupreme

set_option autoImplicit false
set_option Elab.async false

/-! Transfer a chosen bottom reduced supreme plan to its actual source.
No witness full-system bound is assumed, so this interface can be used
inside forest-to-order conversion without circularity. -/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualBottomReducedTransfer

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
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
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




theorem attachedSelectedPicture_two_cut_two_standards_bottom_reduced_supreme
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
    (hBottom : Function.Injective (Wit).parent)
    (hReduced : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSimultaneousSupreme)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hStandards : ∀ k : Fin (cyclicOwnerChanges owner),
      ∃ s : I, Z.label k = Sum.inl s := by
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by have hb := k.isLt; omega
    rcases hk with hZero | hOne
    · have hk0 : k = (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hZero
      exact ⟨i, by simpa only [hk0] using hLabel0⟩
    · have hk1 : k = (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) :=
        Fin.ext hOne
      exact ⟨j, by simpa only [hk1] using hLabel1⟩
  cases hC0 : Z.connector (⟨0, by omega⟩ : Fin (cyclicOwnerChanges owner)) with
  | inl x =>
      cases hC1 : Z.connector (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) with
      | inl y =>
          obtain ⟨b, hBoth⟩ :=
            Z.two_common_edge_of_bottom_supreme_of_length_two
              Wit hBottom hTwo hReduced
          have hPair : (Wit).PairEdge x y := ⟨b,
            by simpa only [hC0, OrderOneData.Incident, OrderOneData.carrier]
              using hBoth ⟨0, by omega⟩,
            by simpa only [hC1, OrderOneData.Incident, OrderOneData.carrier]
              using hBoth ⟨1, by omega⟩⟩
          exact attachedSelectedPicture_two_cut_pairEdge_geometric_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            i j hLabel0 hLabel1 x y hC0 hC1 hPair hOldSupreme
      | inr p =>
          have hMixed :
              (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
               Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
              (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
               Z.connector ⟨1, by omega⟩ = Sum.inl x) := Or.inl ⟨hC0, hC1⟩
          have hBridges := Z.two_mixed_bridges_of_bottom_supreme_of_length_two
            Wit hBottom hTwo hReduced x p hMixed
          exact attachedSelectedPicture_two_cut_mixed_bridges_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            hStandards x p hMixed hBridges hOldSupreme
  | inr p =>
      cases hC1 : Z.connector (⟨1, by omega⟩ : Fin (cyclicOwnerChanges owner)) with
      | inl x =>
          have hMixed :
              (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
               Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
              (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
               Z.connector ⟨1, by omega⟩ = Sum.inl x) := Or.inr ⟨hC0, hC1⟩
          have hBridges := Z.two_mixed_bridges_of_bottom_supreme_of_length_two
            Wit hBottom hTwo hReduced x p hMixed
          exact attachedSelectedPicture_two_cut_mixed_bridges_full_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            hStandards x p hMixed hBridges hOldSupreme
      | inr r =>
          exact False.elim (Z.two_wagon_absurd_of_supreme_of_length_two
            Wit hTwo hReduced p r hC0 hC1)

theorem attachedSelectedPicture_two_cut_bottom_reduced_supreme
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
    (hBottom : Function.Injective (Wit).parent)
    (hReduced : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSimultaneousSupreme)
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
  have hPred1 : trainCyclicPred z1 = z0 := by
    apply Fin.ext
    change (1 + cyclicOwnerChanges owner - 1) %
      cyclicOwnerChanges owner = 0
    rw [hTwo]
  cases hL0 : Z.label z0 with
  | inl i =>
      cases hL1 : Z.label z1 with
      | inl j =>
          exact attachedSelectedPicture_two_cut_two_standards_bottom_reduced_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            i j hL0 hL1 hBottom hReduced hOldSupreme
      | inr b =>
          have hTarget : Z.label (trainCyclicPred z1) =
              Sum.inl i := by
            rw [hPred1]
            exact hL0
          exact attachedSelectedPicture_two_cut_standard_core_reduced_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            z1 i b hTarget hL1 hReduced hOldSupreme
  | inr b =>
      cases hL1 : Z.label z1 with
      | inl i =>
          have hTarget : Z.label (trainCyclicPred z0) =
              Sum.inl i := by
            rw [hPred0]
            exact hL1
          exact attachedSelectedPicture_two_cut_standard_core_reduced_supreme
            A hA B D C family selected e R f T U hShared hRel μ
            hStrong hTwoCopies hOldStrong hCoreStrong
            K hAccept hLinear hn hOrder owner hAllowed hTwo
            z0 i b hTarget hL0 hReduced hOldSupreme
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



/-- At original source length two, a chosen bottom reduced supreme plan
supplies the actual mixed bridges and rules out the two-wagon case. The
retained designated occurrence is still an ORIGINAL source label. -/
theorem attachedSelectedPicture_original_two_bottom_reduced_supreme
    [Finite UA] (q : ℕ) (hq : 1 ≤ q)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧ b.1 ⊆ copyCarrier r.1.embedding)
    (hOldSupreme : (Old).SupremeCycleBound q)
    (K : (Out).BigCycle 2) (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain)
    (owner : Fin 2 → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (hBottom : Function.Injective (Wit).parent)
    (hReduced : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSimultaneousSupreme) :
    K.HasSimultaneousSupreme := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hIndex (j : Fin (cyclicOwnerChanges owner)) :
      cyclicOwnerCutIndex owner j = (⟨j.val, by omega⟩ : Fin 2) :=
    Fin.ext (cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j)
  have hConnector (j : Fin (cyclicOwnerChanges owner)) :
      Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (⟨j.val, by omega⟩ : Fin 2) := by
    have h := attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector A hA B D C family selected e R f T U
        hShared hRel μ K owner hAllowed j) = _
    simpa only [hIndex] using h
  have hMap : Function.Injective (Sum.map CoreEmb CoreWagon) :=
    Sum.map_injective.mpr ⟨(CoreEmb).injective, (CoreWagon).injective⟩
  apply attachedSelectedPicture_original_two_cycle_supreme_of_owner_bridges
    A hA B D C family selected e R f T U hShared hRel μ
    q hq hStrong hTwoCopies hOldSupreme K hAccept hLinear
    owner hAllowed hTwo hOrder
  · intro x p hMixed _hV _hW
    have hMixedZ :
        (Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
         Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
        (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
         Z.connector ⟨1, by omega⟩ = Sum.inl x) := by
      rcases hMixed with h | h
      · exact Or.inl ⟨hMap ((hConnector ⟨0, by omega⟩).trans h.1),
          hMap ((hConnector ⟨1, by omega⟩).trans h.2)⟩
      · exact Or.inr ⟨hMap ((hConnector ⟨0, by omega⟩).trans h.1),
          hMap ((hConnector ⟨1, by omega⟩).trans h.2)⟩
    have hBridges := Z.two_mixed_bridges_of_bottom_supreme_of_length_two
      Wit hBottom hTwo hReduced x p hMixedZ
    intro k
    let j : Fin (cyclicOwnerChanges owner) := ⟨k.val, by omega⟩
    have hj : cyclicOwnerCutIndex owner j = k := by
      apply Fin.ext
      exact cyclicOwnerCutIndex_val_eq_of_source_two owner hTwo j
    have hLabel : Z.label j = owner k := by
      change owner (cyclicOwnerCutIndex owner j) = owner k
      rw [hj]
    simpa only [hLabel] using hBridges j
  · intro p r h0 h1
    exact Z.two_wagon_absurd_of_supreme_of_length_two
      Wit hTwo hReduced p r
      (hMap ((hConnector ⟨0, by omega⟩).trans h0))
      (hMap ((hConnector ⟨1, by omega⟩).trans h1))

/-- Transfer at every source length from one chosen bottom reduced
supreme plan. The only cycle bound is the old picture's bound; the
witness's desired full bound is not an assumption. -/
theorem attachedSelectedPicture_bottom_reduced_supreme
    [Finite UA] (q : ℕ) (hq : 1 ≤ q)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧ b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n) (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hBottom : Function.Injective (Wit).parent)
    (hReduced : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSimultaneousSupreme) :
    K.HasSimultaneousSupreme := by
  have hLength := K.length_ge_two
  by_cases hn : n = 2
  · subst n
    have hCutBound := Fintype.card_le_of_injective (cyclicOwnerCutIndex owner)
      (cyclicOwnerCutIndex owner).injective
    simp only [Fintype.card_fin] at hCutBound
    have hTwo : cyclicOwnerChanges owner = 2 := by omega
    exact attachedSelectedPicture_original_two_bottom_reduced_supreme
      A hA B D C family selected e R f T U hShared hRel μ
      q hq hStrong hTwoCopies hOldSupreme K hAccept hLinear
      owner hAllowed hTwo hOrder hBottom hReduced
  have hn3 : 3 ≤ n := by omega
  by_cases hTwo : cyclicOwnerChanges owner = 2
  · exact attachedSelectedPicture_two_cut_bottom_reduced_supreme
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwoCopies hOldStrong hCoreStrong
      K hAccept hLinear hn3 hOrder owner hAllowed hTwo
      hBottom hReduced hOldSupreme
  have hThree : 3 ≤ cyclicOwnerChanges owner := by omega
  obtain ⟨target, hTarget, pieces, hPlan, hProduces⟩ := hReduced
  cases hLabel : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target with
  | inl i =>
      exact attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound
        A hA B D C family selected e R f T U hShared hRel μ
        hStrong hTwoCopies hOldStrong hCoreStrong
        K hAccept hLinear hn3 hOrder owner hAllowed hThree
        target i hLabel ⟨hTarget, pieces, hPlan, hProduces⟩ hOldSupreme
  | inr b => simp only [hLabel, OrderOneData.designated] at hTarget


/-- The bottom order-one bridge alternative also transfers directly.
The generic singleton-wagon theorem first constructs the reduced global
plan, including its designated occurrence and literal result word. -/
theorem attachedSelectedPicture_bottom_mixed_bridges_supreme
    [Finite UA] (q : ℕ) (hq : 1 ≤ q)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧ b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n) (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hBottom : Function.Injective (Wit).parent)
    (x : Y) (p : Quotient (U.wagonSetoid μ))
    (hMixed :
      ((attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inl x ∧
       (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inr p) ∨
      ((attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inr p ∧
       (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inl x))
    (hBridges : ∀ k : Fin (cyclicOwnerChanges owner),
      (Wit).Bridge
        ((attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label k) x p) :
    K.HasSimultaneousSupreme := by
  apply attachedSelectedPicture_bottom_reduced_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    q hq hStrong hTwoCopies hOldStrong hCoreStrong hOldSupreme
    K hAccept hLinear hOrder owner hAllowed (by omega) hBottom
  exact OrderOneData.BigCycle.two_supreme_of_bottom_mixed_bridges_of_length_two
    Wit hBottom hTwo _ x p hMixed hBridges

end ActualBottomReducedTransfer
end StructuralRamsey.Girth
