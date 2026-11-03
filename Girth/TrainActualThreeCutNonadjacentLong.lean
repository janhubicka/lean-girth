import Girth.TrainActualChosenNonadjacentLongOldUncut
import Girth.TrainActualCoreSingletonConsecutiveCuts
import Mathlib.Tactic

/-!
# Path A: reverse-adjacent original cuts are impossible with three or more cuts

Consecutive indices in the canonical cyclic enumeration of at least three
owner cuts cannot correspond to original positions in the REVERSE cyclic
order. The positive-cut application therefore needs only to rule out
forward adjacency to activate the already verified selected-long
old-wagon/non-cut obstruction.

This is a finite cyclic indexing lemma, not a transfer theorem.
No appendix or manuscript changes.
-/

namespace StructuralRamsey.Girth

universe v

/-- Two cyclic successors are never the identity on Fin n for n ≥ 3. -/
theorem cyclicSucc_succ_ne_self_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    cyclicSucc (cyclicSucc j) ≠ j := by
  have hVal (x : Fin n) :
      (cyclicSucc x).val =
        if x.val + 1 < n then x.val + 1 else 0 := by
    change (x.val + 1) % n =
      if x.val + 1 < n then x.val + 1 else 0
    by_cases h : x.val + 1 < n
    · simp only [if_pos h]
      exact Nat.mod_eq_of_lt h
    · simp only [if_neg h]
      have hLast : x.val + 1 = n := by omega
      rw [hLast, Nat.mod_self]
  intro hEq
  have hOne := hVal j
  have hTwo := hVal (cyclicSucc j)
  have hv := congrArg Fin.val hEq
  rw [hTwo, hOne] at hv
  split_ifs at hv <;> omega

/-- Applying cyclic predecessor twice is not stationary when the
cyclic index set has at least three points. -/
theorem trainCyclicPred_pred_ne_self_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    trainCyclicPred (trainCyclicPred j) ≠ j := by
  intro hEq
  have hOne := congrArg cyclicSucc hEq
  rw [cyclicSucc_trainCyclicPred_of_two_le (by omega : 2 ≤ n)
    (trainCyclicPred j)] at hOne
  have hTwo := congrArg cyclicSucc hOne
  rw [cyclicSucc_trainCyclicPred_of_two_le (by omega : 2 ≤ n) j] at hTwo
  exact (cyclicSucc_succ_ne_self_of_three_le hn j) hTwo.symm

/-- Two consecutive cut positions in the cyclic cut enumeration
can never be reversed-adjacent ORIGINAL positions when at least three
cuts exist. The proof uses the verified adjacent-cuts indexing lemma,
including the last-to-first wrap of the canonical increasing list. -/
theorem cyclicOwnerCutIndex_pred_ne_reverse_succ_of_three_cuts
    {Owner : Type v} {n : ℕ}
    (owner : Fin n → Owner)
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (cut : Fin (cyclicOwnerChanges owner)) :
    cyclicOwnerCutIndex owner (trainCyclicPred cut) ≠
      cyclicSucc (cyclicOwnerCutIndex owner cut) := by
  let a : Fin n := cyclicOwnerCutIndex owner (trainCyclicPred cut)
  let b : Fin n := cyclicOwnerCutIndex owner cut
  intro hReverse
  change a = cyclicSucc b at hReverse
  have hCard : (cyclicOwnerCutPositions owner).card ≤ n := by
    calc
      (cyclicOwnerCutPositions owner).card ≤
          (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hn : 2 ≤ n := by
    rw [cyclicOwnerCutPositions_card owner] at hCard
    omega
  have hACut : a ∈ cyclicOwnerCutPositions owner :=
    (cyclicOwnerCutIndex_mem_iff owner a).mpr
      ⟨trainCyclicPred cut, rfl⟩
  have hBCut : b ∈ cyclicOwnerCutPositions owner :=
    (cyclicOwnerCutIndex_mem_iff owner b).mpr ⟨cut, rfl⟩
  have hPredA : trainCyclicPred a = b := by
    rw [hReverse]
    exact trainCyclicPred_cyclicSucc_of_two_le hn b
  obtain ⟨j, hjA, hjPrevious⟩ :=
    cyclicOwnerCutIndex_pred_of_adjacent_cuts owner hn a
      (by rw [hPredA]; exact hBCut) hACut
  have hj : j = trainCyclicPred cut := by
    apply (cyclicOwnerCutIndex owner).injective
    exact hjA
  subst j
  have hDouble : trainCyclicPred (trainCyclicPred cut) = cut := by
    apply (cyclicOwnerCutIndex owner).injective
    exact hjPrevious.trans hPredA
  exact (trainCyclicPred_pred_ne_self_of_three_le hThree cut) hDouble

open StructuralRamsey.RelStructure

universe u
section ChosenLongThreeCutObstruction

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
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- For ≥3 owner cuts, only FORWARD nonadjacency remains to be checked.
The reverse nonadjacency follows automatically from the canonical cut
order. A chosen long piece must then reuse a genuine ORIGINAL wagon
connector at an uncut position; the plan and piece are actual. -/
theorem attachedSelectedPicture_chosen_forward_nonadjacent_long_old_uncut_wagon
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThreeCuts : 3 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (hNotForward : cyclicOwnerCutIndex owner cut ≠
      cyclicSucc (cyclicOwnerCutIndex owner (trainCyclicPred cut))) :
    let hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∀ (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ)),
        pieces cut = .long first w second →
        ∃ t : Fin n, K.connector t = Sum.inr (CoreWagon w) ∧
          t ∉ cyclicOwnerCutPositions owner) := by
  exact attachedSelectedPicture_chosen_nonadjacent_long_old_uncut_wagon
    A hA B D C family selected e R f T U hShared hRel μ
    K hAccept owner hAllowed (by omega) target cut hSupreme
    hNotForward
    (cyclicOwnerCutIndex_pred_ne_reverse_succ_of_three_cuts
      owner hThreeCuts cut)

end ChosenLongThreeCutObstruction
end StructuralRamsey.Girth
