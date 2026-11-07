import Girth.TrainActualTwoCutDistinctStandards
import Girth.TrainActualReducedShortSingleton
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: a genuine two-cut reduced short determines the singleton source run

The already checked actual source A2/A3 two-contact theorem says that
the two physical original cut endpoints of ANY genuinely valid reduced
short must be cyclically adjacent in one direction.

With EXACTLY TWO geometric owner cuts these two original endpoints
are the entire cut set. Reversing the two-element cut index converts
the reverse-adjacent case into forward adjacency at the OTHER reduced
occurrence. Hence some actual owner run is a singleton, regardless of
which reduced supreme target was initially chosen.

For a source BigCycle with n >= 3 the two orientations cannot both
hold: two steps of cyclic successor do not return to the same source
index. The orientation is thus genuine source geometry, not merely an
artifact of the two-element cut index.

This does NOT reselect a globally valid reduced supreme plan, assert
the new short is owned by the chosen standard, construct the source
replacement, or prove the long / order-one cases. Circulation only.
-/

namespace StructuralRamsey.Girth

universe v

/-- The cyclic predecessor is an involution on a two-element type. -/
theorem trainCyclicPred_pred_eq_self_of_card_two
    {n : ℕ} (hTwo : n = 2) (j : Fin n) :
    trainCyclicPred (trainCyclicPred j) = j := by
  have hp : trainCyclicPred j = cyclicSucc j :=
    trainCyclicPred_eq_cyclicSucc_of_card_two hTwo j
  rw [hp]
  exact trainCyclicPred_cyclicSucc_of_two_le (by omega : 2 ≤ n) j

/-- If two original cut points are forward- and reverse-adjacent
simultaneously, the source cycle has at most two occurrences. -/
theorem cyclicOwnerCutIndex_two_orientations_exclusive
    {Owner : Type v} {n : ℕ}
    (hn : 3 ≤ n) (owner : Fin n → Owner)
    (cut : Fin (cyclicOwnerChanges owner)) :
    ¬ (cyclicOwnerCutIndex owner cut =
          cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) ∧
        cyclicOwnerCutIndex owner (trainCyclicPred cut) =
          cyclicSucc (cyclicOwnerCutIndex owner cut)) := by
  rintro ⟨hForward, hReverse⟩
  have hDouble :
      cyclicSucc (cyclicSucc (cyclicOwnerCutIndex owner cut)) =
        cyclicOwnerCutIndex owner cut := by
    calc
      cyclicSucc (cyclicSucc (cyclicOwnerCutIndex owner cut))
          = cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) := by
              rw [hReverse]
      _ = cyclicOwnerCutIndex owner cut := hForward.symm
  exact (cyclicSucc_succ_ne_self_of_three_le hn
    (cyclicOwnerCutIndex owner cut)) hDouble

open StructuralRamsey.RelStructure

universe u
section ActualTwoCutShortSingleton

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- An actual reduced ShortValid at either of the two geometric cuts
forces at least one ORIGINAL owner run to be a singleton. If its
own run is not forward-adjacent, the other cut's run is singleton.

The physical edge and cut connectors are the genuine typed ones from
the selected-picture attachment, not abstract guessed contacts. -/
theorem attachedSelectedPicture_two_cut_short_some_singleton_run
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target cut : Fin (cyclicOwnerChanges owner))
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).ShortValid Wit target cut b) :
    ∃ singleton : Fin (cyclicOwnerChanges owner),
      cyclicOwnerCutIndex owner singleton =
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred singleton)) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hAdjacent :=
    attachedSelectedPicture_reduced_short_cuts_adjacent
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hCuts target cut b hShort
  rcases hAdjacent with hForward | hReverse
  · exact ⟨cut, hForward⟩
  · refine ⟨trainCyclicPred cut, ?_⟩
    have hPredPred :
        trainCyclicPred (trainCyclicPred cut) = cut :=
      trainCyclicPred_pred_eq_self_of_card_two hTwo cut
    rw [hPredPred]
    exact hReverse

/-- With at least three original source occurrences, the above
actual reduced short determines an EXCLUSIVE adjacency orientation:
there is no two-way adjacency hidden by the two-element quotient. -/
theorem attachedSelectedPicture_two_cut_short_unique_orientation
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target cut : Fin (cyclicOwnerChanges owner))
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).ShortValid Wit target cut b) :
    (cyclicOwnerCutIndex owner cut =
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut)) ∧
      cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
        cyclicSucc (cyclicOwnerCutIndex owner cut)) ∨
    (cyclicOwnerCutIndex owner (trainCyclicPred cut) =
        cyclicSucc (cyclicOwnerCutIndex owner cut) ∧
      cyclicOwnerCutIndex owner cut ≠
        cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  have hAdjacent :=
    attachedSelectedPicture_reduced_short_cuts_adjacent
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hCuts target cut b hShort
  have hNotBoth :=
    cyclicOwnerCutIndex_two_orientations_exclusive hn owner cut
  rcases hAdjacent with hf | hr
  · exact Or.inl ⟨hf, fun hr => hNotBoth ⟨hf, hr⟩⟩
  · exact Or.inr ⟨hr, fun hf => hNotBoth ⟨hf, hr⟩⟩

end ActualTwoCutShortSingleton
end StructuralRamsey.Girth
