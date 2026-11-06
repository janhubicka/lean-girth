import Girth.TrainCyclicExpandReducedPieces
import Girth.TrainActualPositiveCutLongPhysicalLift
import Girth.TrainActualPlanLongFreshThreeCuts
import Mathlib.Tactic

/-!
# Path A: long pieces of the expanded source plan have A2 geometry and freshness

The total run-to-source expansion inserts a long piece ONLY at a
singleton original occurrence whose two canonical cut connectors
are its actual left/right source boundaries. Its physical edge and
wagon labels are exactly the images of ONE specific reduced long piece.

The actual reduced LongValid geometry therefore lifts to physical
source LocalLongA2Geometry, and the checked fixed-plan singleton-long
freshness lemma supplies freshness against EVERY original source
connector. No identification of unrelated existential plans occurs.

Short-piece incidence on singleton/two-step source runs remains a
different obligation. No appendix or manuscript changes.
-/

namespace StructuralRamsey.Girth

universe v
variable {Owner E P F Q : Type v} {n : ℕ}

/-- Invert an actual source-expanded LONG piece. It can arise only
from a reduced long at a singleton original source occurrence:
the original source position is the selected run-ending cut, and the
previous reduced cut is precisely the original cyclic predecessor.

This is a pure finite piece-constructor statement, including wrap. -/
theorem cyclicExpandReducedPieces_long_inverse
    (owner : Fin n → Owner)
    (hCuts : 0 < cyclicOwnerChanges owner)
    (reduced : Fin (cyclicOwnerChanges owner) → TrainSupremePiece E P)
    (edge : E → F) (wagon : P → Q)
    (pos : Fin n) (a : F) (p : Q) (b : F)
    (hOut : cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
      .long a p b) :
    ∃ (j : Fin (cyclicOwnerChanges owner)) (first : E)
      (w : P) (second : E),
      cyclicOwnerRunIndex owner hCuts pos = j ∧
      reduced j = .long first w second ∧
      pos = cyclicOwnerCutIndex owner j ∧
      cyclicOwnerCutIndex owner (trainCyclicPred j) =
        trainCyclicPred pos ∧
      edge first = a ∧ wagon w = p ∧ edge second = b := by
  classical
  let j := cyclicOwnerRunIndex owner hCuts pos
  have hUnfold :
      cyclicExpandReducedPieces owner hCuts reduced edge wagon pos =
        match reduced j with
        | .keep => .keep
        | .short e => .short (edge e)
        | .long first w second =>
            if pos = cyclicOwnerCutIndex owner j then
              if cyclicOwnerCutIndex owner (trainCyclicPred j) =
                  trainCyclicPred pos then
                .long (edge first) (wagon w) (edge second)
              else .short (edge second)
            else .short (edge first) := rfl
  rw [hUnfold] at hOut
  cases hp : reduced j with
  | keep =>
      simp only [hp] at hOut
  | short e =>
      simp only [hp] at hOut
  | long first w second =>
      by_cases hAt : pos = cyclicOwnerCutIndex owner j
      · by_cases hPrevious :
          cyclicOwnerCutIndex owner (trainCyclicPred j) =
            trainCyclicPred pos
        · have hMapped :
            (TrainSupremePiece.long (edge first) (wagon w) (edge second) :
              TrainSupremePiece F Q) = .long a p b := by
            simpa only [hp, if_pos hAt, if_pos hPrevious] using hOut
          have hFields :
              edge first = a ∧ wagon w = p ∧ edge second = b := by
            simpa using hMapped
          exact ⟨j, first, w, second, rfl, hp, hAt, hPrevious,
            hFields.1, hFields.2.1, hFields.2.2⟩
        · simp only [hp, if_pos hAt, if_neg hPrevious] at hOut
      · simp only [hp, if_neg hAt] at hOut

open StructuralRamsey.RelStructure

universe u
section ActualExpandedLongGeometry

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- For any specified valid reduced plan, all actual LONG pieces
surviving its literal source expansion satisfy the exact physical
A2 geometry, including the ambient no-pair-edge condition.
The original source need not have a designated copy label naming i. -/
theorem attachedSelectedPicture_expanded_plan_localLongA2Geometry
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).PlanValid Wit target pieces) :
    K.LocalLongA2Geometry Out
      (cyclicExpandReducedPieces owner (by omega) pieces
        CoreActual CoreWagon) := by
  intro pos a b p hp
  obtain ⟨j, first, w, second, _hj, hReducedLong,
    hThis, hPrevious, he, hw, hf⟩ :=
    cyclicExpandReducedPieces_long_inverse
      owner (by omega) pieces CoreActual CoreWagon pos a p b hp
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  have hDiff : Z.label j ≠ Z.label target := by
    intro heq
    have hk := (hPlan j).1 heq
    have impossible :
        (TrainSupremePiece.long first w second :
          TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ))) =
          TrainSupremePiece.keep := hReducedLong.symm.trans hk
    cases impossible
  have hLong : Z.LongValid Wit target j first w second := by
    have hc := (hPlan j).2 hDiff
    simpa only [hReducedLong] using hc
  have hPhysical : K.PhysicalLongGeometry Out pos
      (CoreActual first) (CoreWagon w) (CoreActual second) :=
    attachedSelectedPicture_reduced_long_piece_physical_output
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts hActive target j
      first second w hLong pos hThis.symm hPrevious
  obtain ⟨x, y, hLeft, hRight, _hNe, hParFirst, hParSecond,
    hx, hy, hNoPair⟩ := hPhysical
  rw [← hw]
  exact ⟨x, y, hLeft, hRight,
    ⟨CoreActual first, hParFirst, hx⟩,
    ⟨CoreActual second, hParSecond, hy⟩, hNoPair⟩

/-- Under THREE or more source owner cuts, a SPECIFIED globally legal
reduced plan inserts no original long wagon at any already existing
original connector. This is the global freshness hypothesis for the
actual arbitrary-replacement theorem, without replacing the plan
by a different existential witness. -/
theorem attachedSelectedPicture_expanded_plan_long_fresh
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hActive : AStrong A C.toRelStructure S)
    (target : Fin (cyclicOwnerChanges owner))
    (pieces : Fin (cyclicOwnerChanges owner) →
      TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)))
    (hPlan : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanValid Wit target pieces)
    (hProduces : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).PlanProducesBigCycle Wit pieces) :
    ∀ (pos : Fin n)
      (a : OldACarrierEdge A
        (RelStructure.Attachment.attach C.toRelStructure S R f))
      (p : Quotient ((generatedActualASupportTrain A hA
        C.toRelStructure S R f T U hShared).wagonSetoid μ))
      (b : OldACarrierEdge A
        (RelStructure.Attachment.attach C.toRelStructure S R f)),
      cyclicExpandReducedPieces owner (by omega) pieces CoreActual
        CoreWagon pos = .long a p b →
      ∀ t : Fin n, K.connector t ≠ Sum.inr p := by
  intro pos a p b hp
  obtain ⟨j, first, w, second, _hj, hReducedLong,
    hThis, hPrevious, he, hw, hf⟩ :=
    cyclicExpandReducedPieces_long_inverse
      owner (by omega) pieces CoreActual CoreWagon pos a p b hp
  have hFresh :
      ∀ t : Fin n, K.connector t ≠ Sum.inr (CoreWagon w) :=
    attachedSelectedPicture_plan_long_fresh_of_three_cuts
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept hn owner hAllowed hThree hActive
      target j pieces hPlan hProduces pos
      hThis.symm hPrevious first second w hReducedLong
  intro t
  simpa only [← hw] using hFresh t

end ActualExpandedLongGeometry
end StructuralRamsey.Girth
