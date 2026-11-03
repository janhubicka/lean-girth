import Girth.TrainActualReducedLongRankDescent
import Girth.TrainActualChosenLongFreshThreeCuts
import Mathlib.Tactic

/-!
# Path A: selected singleton long pieces descend with three or more cuts

For an actual chosen supreme plan, an ORIGINAL singleton segment has
consecutive cut connectors. When the source has at least three geometric
owner changes, the actual chosen long wagon is globally fresh (#762).
The exact physical owner-word and minimum geometric lex rank arguments
(#761) therefore give strict descent WITHOUT requiring every source
position to be a cut.

This is a conditional selected-long result, not proof that a chosen
piece is long or that a non-singleton segment admits a fresh insertion.
No appendix or manuscript markers.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualThreeCutChosenSingletonLongRank

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
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A globally CHOSEN legal supreme plan with at least three source
owner cuts gives a smaller minimum geometric/designated lex rank when
the chosen piece at an ORIGINAL singleton (adjacent cut connectors)
is long. No all-source-positions-cut assumption is required. -/
theorem attachedSelectedPicture_three_cuts_chosen_singleton_long_rank
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThreeCuts : 3 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).HasSupremeAt Wit target)
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target = Sum.inl i)
    (hAdjacent : cyclicOwnerCutIndex owner cut =
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
        ∃ outLength : ℕ, ∃ H : (Out).BigCycle outLength,
          H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
          (∀ kH : Fin outLength, H.HasSupremeAt Out kH →
            ∃ kK : Fin n, K.label kK = H.label kH ∧
              K.HasSupremeAt Out kK) ∧
          ∃ minimumOwner : Fin outLength → I ⊕ CoreEdge,
            (∀ k, GeomAllowed (H.label k) (minimumOwner k)) ∧
            (∀ other : Fin outLength → I ⊕ CoreEdge,
              (∀ k, GeomAllowed (H.label k) (other k)) →
              cyclicOwnerChanges minimumOwner ≤ cyclicOwnerChanges other) ∧
            Prod.Lex (· < ·) (· < ·)
              (cyclicOwnerChanges minimumOwner,
                H.designatedOccurrenceCount Out)
              (cyclicOwnerChanges owner,
                K.designatedOccurrenceCount Out)) := by
  classical
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  let pos := cyclicOwnerCutIndex owner cut
  have hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos := by
    dsimp [pos]
    rw [hAdjacent]
    exact (trainCyclicPred_cyclicSucc_of_two_le
      (by omega : 2 ≤ n)
      (cyclicOwnerCutIndex owner (trainCyclicPred cut))).symm
  obtain ⟨pieces, hPlan, hProduces, hFresh⟩ :=
    attachedSelectedPicture_chosen_long_fresh_of_three_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThreeCuts hActive
      target cut hSupreme pos rfl hPrevious
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro first second w hp
  have hDifferent : Z.label cut ≠ Z.label target := by
    intro heq
    have hKeep := (hPlan cut).1 heq
    have hImpossible :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hKeep
    cases hImpossible
  have hLong : Z.LongValid Wit target cut first w second := by
    have hCase := (hPlan cut).2 hDifferent
    simpa only [hp] using hCase
  obtain ⟨outLength, H, _hWord, hOutAccept, hOrder,
    hPull, minOwner, hMinAllowed, hMin, hRank⟩ :=
    attachedSelectedPicture_fresh_long_minimal_designated_rank
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hLinear hn owner hAllowed hCuts hActive
      target cut i hTarget first second w hLong
      pos rfl hPrevious (hFresh first second w hp)
  exact ⟨outLength, H, hOutAccept, hOrder, hPull,
    minOwner, hMinAllowed, hMin, hRank⟩

end ActualThreeCutChosenSingletonLongRank
end StructuralRamsey.Girth
