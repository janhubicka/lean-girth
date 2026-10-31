import Girth.TrainActualPositiveCutLongPhysicalLift

/-!
# Actual reduced long piece -> globally legal fresh-wagon insertion

This is the first-stage physical transfer for a genuine long piece of
the cut-indexed witness. It preserves the critical distinction:
the witness's supreme standard need NOT be a designated label of
the ORIGINAL selected-picture cycle. Only real physical A-support
edges, the exact source boundary positions, strong core nonpair
reflection and fresh wagon are used.

The checked arbitrary-replacement theorem then CONSTRUCTS the entire
literal output BigCycle, checks its acceptability and exact twice-order,
and pulls back any later indexed supreme designated label.

No claim that the expanded cycle has fewer geometric owner cuts is
made. Proving that combinatorial n -> n+1 cut decrease is still a
separate task. No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualPositiveCutFreshLongTransfer

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
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The genuinely reduced long piece supplies the two physical
edges needed by an arbitrary one-long insertion into the ORIGINAL
selected output. If that output wagon is fresh, there is a globally
legal, acceptable replacement cycle with unchanged numerical order,
and EVERY later designated supreme label pulls back.

No original designated supreme target, output-word legality, or
independent physical replacement edge is postulated. -/
theorem attachedSelectedPicture_reduced_fresh_long_global_transfer
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target cut : Fin (cyclicOwnerChanges owner))
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).LongValid Wit target cut first w second)
    (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos)
    (hFresh : ∀ t : Fin n, K.connector t ≠ Sum.inr (CoreWagon w)) :
    ∃ outLength : ℕ, ∃ H : (Out).BigCycle outLength,
      List.ofFn (fun k : Fin outLength => (H.label k, H.connector k)) =
        K.resultWord Out
          (K.onlyLongPieces Out pos (CoreActual first)
            (CoreWagon w) (CoreActual second)) ∧
      H.Acceptable ∧ H.twiceOrder = K.twiceOrder ∧
      (∀ kH : Fin outLength, H.HasSupremeAt Out kH →
        ∃ kK : Fin n, K.label kK = H.label kH ∧
          K.HasSupremeAt Out kK) := by
  have hPhysical : K.PhysicalLongGeometry Out pos
      (CoreActual first) (CoreWagon w) (CoreActual second) :=
    attachedSelectedPicture_reduced_long_piece_physical_output
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hActive
      target cut first second w hLong pos hThis hPrevious
  exact K.oneFreshPhysicalLong_complete_of_three_le
    Out hAccept hLinear hn pos (CoreActual first)
    (CoreWagon w) (CoreActual second) hPhysical hFresh

end ActualPositiveCutFreshLongTransfer
end StructuralRamsey.Girth
