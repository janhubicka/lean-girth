import Girth.TrainActualBottomForestReducedSupreme
import Girth.TrainActualTwoCutStandardCoreShortSupreme
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Bottom forest transfer: exactly two cuts, standard/core owner pair

The existing genuine two-cut standard/core source proof uses the FULL
lower witness bound only once: to obtain a global supreme plan for
the two-label reduced witness. At bottom that plan follows instead
from the local mixed forest through q, with no prior A1 hypothesis.

The remaining verified steps are unchanged: a designated reduced
standard must be supreme, its actual short edge at the core singleton
is extracted, the singleton cut indices are literal, and the checked
source standard-contained short transfer recovers an ORIGINAL
B-labelled supreme copy. No long piece is possible at bottom.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section BottomTwoCutStandardCore

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

/-- Original B-labelled full supremacy for one standard/core pair of
genuine geometric two-cut labels, from the mixed-forest local witness.
No full lower-witness system-girth hypothesis is required. -/
theorem attachedSelectedPicture_bottom_two_cut_standard_core_forest_supreme
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ r : Selected, ∃ a c : OldEdge,
      a ≠ c ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        c.1 ⊆ copyCarrier r.1.embedding)
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
    (hTwo : cyclicOwnerChanges owner = 2)
    (cut : Fin (cyclicOwnerChanges owner)) (i : I) (b : CoreEdge)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μBottom
      K owner hAllowed (by omega)).label (trainCyclicPred cut) = Sum.inl i)
    (hSource : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μBottom
      K owner hAllowed (by omega)).label cut = Sum.inr b) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts
  have hBudget : cyclicOwnerChanges owner ≤ q := by
    have hLen := K.length_le_twiceOrder
    omega
  have hSupreme : Z.HasSimultaneousSupreme :=
    attachedSelectedPicture_bottom_reduced_supreme_of_localForest
      A hA B D C family selected e R f T U hShared hRel
      H q hLocal K owner hAllowed hCuts hBudget
      hAccept.2.1 hAccept.2.2
  obtain ⟨k, hk, pieces, hPlan, hProduces⟩ := hSupreme
  have hkEq : k = trainCyclicPred cut := by
    have hkc : k ≠ cut := by
      intro heq
      subst k
      have hFalse : False := by
        have hDesignated : Wit.designated (Z.label cut) := hk
        rw [hSource] at hDesignated
        exact hDesignated
      exact hFalse.elim
    have hPredNe : trainCyclicPred cut ≠ cut := by
      intro heq
      have hSucc := cyclicSucc_trainCyclicPred_of_two_le hCuts cut
      rw [heq] at hSucc
      exact (cyclicSucc_ne_self_of_two_le hCuts cut) hSucc
    apply Fin.ext
    have hkBound := k.isLt
    have hCutBound := cut.isLt
    have hPredBound := (trainCyclicPred cut).isLt
    have hkVal : k.val ≠ cut.val := by
      intro h
      exact hkc (Fin.ext h)
    have hPredVal : (trainCyclicPred cut).val ≠ cut.val := by
      intro h
      exact hPredNe (Fin.ext h)
    omega
  subst k
  have hAt : Z.HasSupremeAt Wit (trainCyclicPred cut) :=
    ⟨hk, pieces, hPlan, hProduces⟩
  obtain ⟨_pieces, bridge, _hPlan, _hGlobal, _hSelected, hShort⟩ :=
    Z.hasSupremeAt_short_of_edge_label
      Wit (trainCyclicPred cut) cut i b hTarget hSource hAt
  let pos : Fin n := cyclicOwnerCutIndex owner cut
  have hCoreOwner : owner pos = Sum.inr b := by
    change owner (cyclicOwnerCutIndex owner cut) = Sum.inr b at hSource
    exact hSource
  obtain ⟨j, hHere, hPrev⟩ :=
    attachedSelectedPicture_core_singleton_consecutive_cut_indices
      A hA B D C family selected e R f T U hShared μBottom
      K owner hAllowed pos b hCoreOwner
  have hjEq : j = cut := by
    apply (cyclicOwnerCutIndex owner).injective
    simpa [pos] using hHere
  have hPrevious :
      cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        trainCyclicPred pos := by
    rw [← hjEq]
    exact hPrev
  have hForward :
      cyclicOwnerCutIndex owner cut =
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) := by
    change pos =
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))
    rw [hPrevious]
    exact (cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ n) pos).symm
  exact attachedSelectedPicture_two_cut_singleton_short_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μBottom
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hOutputLinear hn hOrder
    owner hAllowed hTwo cut hForward i hTarget
    bridge hShort hOldSupreme

end BottomTwoCutStandardCore
end StructuralRamsey.Girth
