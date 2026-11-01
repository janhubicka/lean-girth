import Girth.TrainActualFullCutLongFreshness
import Girth.TrainActualPositiveCutFreshLongGlobal
import Girth.TrainIsolatedOwnerCutAlignment

/-!
# A long piece from the ACTUAL global supreme plan yields legal output

The actual reduced HasSupremeAt premise provides a complete globally
legal chosen plan, not an arbitrarily selected local LongValid piece.
The checked plan-freshness theorem ensures that every selected long
piece is absent from all original connectors when all original owner
positions are retained cuts. PlanValid identifies the same chosen
piece as a genuine LongValid witness for the selected target.

With the exact original cut-index alignment and active A-strongness,
the checked actual physical-only long transfer constructs the literal
globally acceptable expanded cycle of the same numerical order and
pulls back every subsequently supreme designated label.

No new owner assignment, minimal cut descent, n=3 extraction,
or general theorem for partially retained source cuts is claimed.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
/-- If all original positions are cuts, the predecessor in the
canonical cut index has EXACTLY the predecessor original position.
No extra geometric cut alignment premise is needed. -/
theorem cyclicOwnerCutIndex_pred_of_every_cut
    {Owner : Type v} {n : ℕ} (owner : Fin n → Owner)
    (hn : 2 ≤ n)
    (hEveryCut : ∀ k : Fin n,
      owner k ≠ owner (cyclicSucc k))
    (cut : Fin (cyclicOwnerChanges owner)) :
    cyclicOwnerCutIndex owner (trainCyclicPred cut) =
      trainCyclicPred (cyclicOwnerCutIndex owner cut) := by
  let pos := cyclicOwnerCutIndex owner cut
  have hPrev : owner (trainCyclicPred pos) ≠ owner pos := by
    simpa only [cyclicSucc_trainCyclicPred_of_two_le hn pos] using
      hEveryCut (trainCyclicPred pos)
  obtain ⟨j, hj, hPrevIndex⟩ :=
    cyclicOwnerCutIndex_pred_of_isolated
      owner hn pos hPrev (hEveryCut pos)
  have hEq : j = cut := (cyclicOwnerCutIndex owner).injective hj
  simpa only [hEq, pos] using hPrevIndex

section ActualSupremeChosenLongGlobal

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

local notation "CoreEdge" => OldACarrierEdge A R
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f
    (physicalCoreEdge
      (sharedOldACarrierInclusion A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding)) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding) R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A chosen LONG piece in the real reduced globally supreme plan,
with every original position a geometric cut, gives an actual
legal globally acceptable output. The selected physical edges,
the new wagon and all unchanged original labels are literal.
This is intentionally conditional on actual cut-index alignment. -/
theorem attachedSelectedPicture_supreme_chosen_long_global_of_all_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hEveryCut : ∀ k : Fin n, owner k ≠ owner (cyclicSucc k))
    (hActive : AStrong A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding))
    (target cut : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target)
    (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos) :
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
          List.ofFn (fun k : Fin outLength =>
            (H.label k, H.connector k)) =
            K.resultWord Out
              (K.onlyLongPieces Out pos (CoreActual first)
                (CoreWagon w) (CoreActual second)) ∧
          H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
          (∀ kH : Fin outLength, H.HasSupremeAt Out kH →
            ∃ kK : Fin n, K.label kK = H.label kH ∧
              K.HasSupremeAt Out kK)) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hFresh⟩ :=
    attachedSelectedPicture_supreme_long_wagon_fresh_of_all_source_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hEveryCut target hSupreme
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro first second w hp
  have hDifferent : Z.label cut ≠ Z.label target := by
    intro heq
    have hKeep := (hPlan cut).1 heq
    cases hKeep
  have hLong : Z.LongValid Wit target cut first w second := by
    have hCase := (hPlan cut).2 hDifferent
    simpa only [hp] using hCase
  exact attachedSelectedPicture_reduced_fresh_long_global_transfer
    A hA B D C family selected e R f T U hShared hRel μ
    K hAccept hLinear hn owner hAllowed hCuts hActive
    target cut first second w hLong pos hThis hPrevious
    (hFresh cut first second w hp)

end ActualSupremeChosenLongGlobal
end StructuralRamsey.Girth
