import Girth.TrainActualBottomForestReducedSupreme
import Girth.TrainActualTwoCutSymmetricShortSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Bottom forest transfer: exactly two cuts, TWO designated standards

The actual reduced witness has exactly two labels, both gluing-copy
standards. Its finite mixed-forest bound forces ONE COMMON physical
support edge belonging to both standards and incident with both
original reduced connectors. The already verified symmetric-short
two-cut source theorem then produces a globally supreme ORIGINAL
B-copy of the source cycle.

There is no full witness system girth hypothesis, no fresh long piece,
and no new physical source replacement theorem.
The standard/core and original source length-two cases are separate.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section BottomTwoStandard

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

/-- Conditional original B-labelled supremeness at an ACTUAL two-cut
source assignment, when both reduced owners are distinct designated
standards. A size-q local forest replaces the full witness bound. -/
theorem attachedSelectedPicture_bottom_two_standard_supreme_of_localForest
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
    (q : ℕ)
    (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (i j : I)
    (hLabel0 :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μBottom
        K owner hAllowed (by omega)).label ⟨0, by omega⟩ = Sum.inl i)
    (hLabel1 :
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μBottom
        K owner hAllowed (by omega)).label ⟨1, by omega⟩ = Sum.inl j) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts
  let z0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  let z1 : Fin (cyclicOwnerChanges owner) := ⟨1, by omega⟩
  have hSucc0 : cyclicSucc z0 = z1 := by
    apply Fin.ext
    change (0 + 1) % cyclicOwnerChanges owner = 1
    rw [hTwo]
  have hSucc1 : cyclicSucc z1 = z0 := by
    apply Fin.ext
    change (1 + 1) % cyclicOwnerChanges owner = 0
    rw [hTwo]
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
  have hq : 2 ≤ q := by
    have hl := K.length_le_twiceOrder
    omega
  have hForest : Z.BottomForest Wit H :=
    Z.bottomForest_of_localForest Wit H q hLocal (by omega)
  let a : Set.range Z.label := ⟨Z.label z0, ⟨z0, rfl⟩⟩
  let b : Set.range Z.label := ⟨Z.label z1, ⟨z1, rfl⟩⟩
  have hab : a ≠ b := by
    intro h
    have hVal := congrArg Subtype.val h
    have hDiff := Z.adjacent_ne z0
    rw [hSucc0] at hDiff
    exact hDiff (by simpa [a, b] using hVal)
  have hAllowedPair : AllowedIntersection
      (Wit.bottomForestPiece H (Z.label z0))
      (Wit.bottomForestPiece H (Z.label z1)) :=
    hForest.pairwiseAllowed hab
  have hNeConn : Z.connector z0 ≠ Z.connector z1 := by
    intro h
    have heq := Z.connector_injective h
    have hvals := congrArg Fin.val heq
    exact (by omega : False)
  have hInc00 : Wit.Incident (Z.label z0) (Z.connector z0) :=
    Z.left_incident z0
  have hInc01 : Wit.Incident (Z.label z0) (Z.connector z1) := by
    have hh := Z.right_incident z1
    rw [hSucc1] at hh
    exact hh
  have hInc10 : Wit.Incident (Z.label z1) (Z.connector z0) := by
    have hh := Z.right_incident z0
    rw [hSucc0] at hh
    exact hh
  have hInc11 : Wit.Incident (Z.label z1) (Z.connector z1) :=
    Z.left_incident z1
  obtain ⟨edge, he0, he1, hEdge0, hEdge1⟩ :=
    H.common_short_edge Wit hAllowedPair hNeConn
      hInc00 hInc01 hInc10 hInc11
  have hStandards : ∀ k : Fin (cyclicOwnerChanges owner),
      ∃ s : I, Z.label k = Sum.inl s := by
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by
      have hb := k.isLt
      omega
    rcases hk with hk0 | hk1
    · have heq : k = z0 := Fin.ext hk0
      subst k
      exact ⟨i, hLabel0⟩
    · have heq : k = z1 := Fin.ext hk1
      subst k
      exact ⟨j, hLabel1⟩
  have hEveryShort : ∀ k : Fin (cyclicOwnerChanges owner),
      Z.ShortValid Wit (trainCyclicPred k) k edge := by
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by
      have hb := k.isLt
      omega
    rcases hk with hk0 | hk1
    · have heq : k = z0 := Fin.ext hk0
      subst k
      rw [hPred0]
      exact ⟨he1, hEdge1, hEdge0⟩
    · have heq : k = z1 := Fin.ext hk1
      subst k
      rw [hPred1]
      exact ⟨he0, hEdge0, hEdge1⟩
  exact attachedSelectedPicture_two_cut_symmetric_short_supreme
    A hA B D C family selected e R f T U hShared hRel μBottom
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hOutputLinear hn hOrder
    owner hAllowed hTwo hStandards edge hEveryShort hOldSupreme

end BottomTwoStandard
end StructuralRamsey.Girth
