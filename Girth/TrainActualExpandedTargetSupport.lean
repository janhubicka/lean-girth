import Girth.TrainCyclicExpandReducedPieces
import Girth.TrainActualPositiveCutShortPieceLift
import Girth.TrainActualLongStandardSupport
import Mathlib.Tactic

/-!
# Path A: every expanded non-kept physical edge lies in the chosen standard

The one-pass source plan is expanded from one specified globally chosen
reduced PlanValid witness. A physical edge that is SHORT in the source
plan may come from either a reduced short or one of the two edges of a
reduced long; a physical LONG in the source plan comes from a reduced
long at an original singleton owner run.

The finite lemma transports any predicate on mapped physical edges
through that short/long source-plan expansion. The actual selected-
picture specialization uses checked genuine reduced ShortValid and
LongValid support results to show all such edges lie in the chosen
attached standard i. No source label-copy identity is assumed.

This is exactly the hShort/hLong pair for the already checked
one-pass standard-transfer theorem, not a construction of a legal
original-cycle replacement. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner E P F Q : Type v} {n : ℕ}

/-- Any property of the selected PHYSICAL edges survives the literal
run-to-source expansion. Both edges of a reduced long must have the
property, since a singleton long uses both and a two-step long uses
them separately as shorts. -/
theorem cyclicExpandReducedPieces_edge_property
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (Pgood : F → Prop)
    (hShort : ∀ (j : Fin (cyclicOwnerChanges owner)) (e : E),
      reduced j = .short e → Pgood (edge e))
    (hLong : ∀ (j : Fin (cyclicOwnerChanges owner))
      (e : E) (p : P) (f : E),
      reduced j = .long e p f →
        Pgood (edge e) ∧ Pgood (edge f))
    (pos : Fin n) :
    match cyclicExpandReducedPieces owner hCuts reduced edge wagon pos with
    | .keep => True
    | .short e => Pgood e
    | .long e _ f => Pgood e ∧ Pgood f := by
  classical
  let j := cyclicOwnerRunIndex owner hCuts pos
  cases hp : reduced j with
  | keep =>
      simp only [cyclicExpandReducedPieces, hp]
  | short e =>
      simpa only [cyclicExpandReducedPieces, hp] using
        (hShort j e hp)
  | long first w second =>
      have h := hLong j first w second hp
      by_cases hAt : pos = cyclicOwnerCutIndex owner j
      · by_cases hPrevious :
          cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred pos
        · simpa only [cyclicExpandReducedPieces, hp, if_pos hAt, if_pos hPrevious]
            using h
        · simpa only [cyclicExpandReducedPieces, hp, if_pos hAt, if_pos hPrevious]
            using h.2
      · simpa only [cyclicExpandReducedPieces, hp, if_neg hAt] using h.1

open StructuralRamsey.RelStructure

universe u
section ActualExpandedTargetSupport

variable {L : RelLanguage.{u}} {UA VB PP X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L PP)
variable (C : StructuralRamsey.Partite.System L PP X)
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
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- For one specified genuine reduced PlanValid witness, every
physical short and both edges of every physical long in its
source-expanded plan lie in the SAME actual attached standard i.
The original source labels need not be designated copies with index i.

This proves hShort and hLong of the checked standard-transfer theorem,
conditionally on the one-pass source plan being physically legal. -/
theorem attachedSelectedPicture_expanded_plan_edges_in_target_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner))
    (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).PlanValid Wit target pieces) :
    (∀ (pos : Fin n) (edge : OldACarrierEdge A
      (RelStructure.Attachment.attach C.toRelStructure S R f)),
      cyclicExpandReducedPieces owner (by omega) pieces CoreActual
        CoreWagon pos = .short edge →
      edge.1 ⊆ copyCarrier (Std i)) ∧
    (∀ (pos : Fin n)
      (edge : OldACarrierEdge A
        (RelStructure.Attachment.attach C.toRelStructure S R f))
      (wagon : Quotient ((generatedActualASupportTrain A hA
        C.toRelStructure S R f T U hShared).wagonSetoid μ))
      (other : OldACarrierEdge A
        (RelStructure.Attachment.attach C.toRelStructure S R f)),
      cyclicExpandReducedPieces owner (by omega) pieces CoreActual
        CoreWagon pos = .long edge wagon other →
      edge.1 ⊆ copyCarrier (Std i) ∧
      other.1 ⊆ copyCarrier (Std i)) := by
  classical
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hShort (j : Fin (cyclicOwnerChanges owner)) (b : CoreEdge)
      (hp : pieces j = .short b) :
      (CoreActual b).1 ⊆ copyCarrier (Std i) := by
    have hDiff : Z.label j ≠ Z.label target := by
      intro heq
      have hk := (hPlan j).1 heq
      have hf : (TrainSupremePiece.short b :
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hk
      cases hf
    have hValid : Z.ShortValid Wit target j b := by
      have hc := (hPlan j).2 hDiff
      simpa only [hp] using hc
    exact attachedSelectedPicture_cut_short_piece_carrier_in_standard
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target j i hTarget b hValid
  have hLong (j : Fin (cyclicOwnerChanges owner))
      (first : CoreEdge) (w : Quotient (U.wagonSetoid μ))
      (second : CoreEdge)
      (hp : pieces j = .long first w second) :
      (CoreActual first).1 ⊆ copyCarrier (Std i) ∧
      (CoreActual second).1 ⊆ copyCarrier (Std i) := by
    have hDiff : Z.label j ≠ Z.label target := by
      intro heq
      have hk := (hPlan j).1 heq
      have hf : (TrainSupremePiece.long first w second :
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hp.symm.trans hk
      cases hf
    have hValid : Z.LongValid Wit target j first w second := by
      have hc := (hPlan j).2 hDiff
      simpa only [hp] using hc
    exact sharedWitness_long_piece_physical_edges_in_standard
      A hA D C e R f U μ Z target j
      first second w hValid i hTarget
  have hEvery (pos : Fin n) :
      match cyclicExpandReducedPieces owner (by omega) pieces
        CoreActual CoreWagon pos with
      | .keep => True
      | .short edge => edge.1 ⊆ copyCarrier (Std i)
      | .long edge _ other =>
          edge.1 ⊆ copyCarrier (Std i) ∧
          other.1 ⊆ copyCarrier (Std i) := by
    apply cyclicExpandReducedPieces_edge_property
      owner (by omega) pieces CoreActual CoreWagon
      (fun e => e.1 ⊆ copyCarrier (Std i))
      hShort hLong pos
  constructor
  · intro pos edge hp
    have h := hEvery pos
    simpa only [hp] using h
  · intro pos edge wagon other hp
    have h := hEvery pos
    simpa only [hp] using h

end ActualExpandedTargetSupport
end StructuralRamsey.Girth
