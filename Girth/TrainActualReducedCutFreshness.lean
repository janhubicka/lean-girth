import Girth.TrainActualCutIndexedBigCycle
import Girth.TrainOptionalFreshnessConverse

/-!
# Genuine global supreme plans exclude old wagons at reduced source cuts

The source BigCycle's cut connectors are exact images of the reduced
witness connectors. A globally legal supreme replacement must not
insert a wagon already among the *reduced* connectors; pull this
freshness back to every original connector retained as a source cut.

This is the precise obstruction needed for the exceptional length-three
designated-singleton case. It does not yet prove that every original
connector is a cut; thus freshness at all original connectors and
the full minimum-owner descent remain separate obligations.
Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualReducedCutFreshness

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
local notation "CoreEmb" =>
  RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
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

/-- Freshness at ALL reduced connectors transports to freshness at
EVERY original source connector that survives as a cut. This is
intentionally not freshness at unretained interior connectors. -/
theorem attachedSelectedPicture_reduced_wagon_fresh_at_all_source_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (w : Quotient (U.wagonSetoid μ))
    (hReducedFresh : ∀ j : Fin (cyclicOwnerChanges owner),
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed hCuts).connector j ≠ Sum.inr w) :
    ∀ j : Fin (cyclicOwnerChanges owner),
      K.connector (cyclicOwnerCutIndex owner j) ≠
        Sum.inr (CoreWagon w) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  intro j hOldWagon
  have hMap : Sum.map CoreEmb CoreWagon (Z.connector j) =
      K.connector (cyclicOwnerCutIndex owner j) := by
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
    exact attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  cases hz : Z.connector j with
  | inl x =>
      have hContr := hMap.trans hOldWagon
      simp [hz] at hContr
  | inr q =>
      have hWq : CoreWagon q = CoreWagon w := by
        have h := hMap.trans hOldWagon
        simpa [hz] using h
      have hq : q = w := CoreWagon.injective hWq
      apply hReducedFresh j
      simpa [hz, hq]

/-- A full HasSupremeAt plan constructs its replacement word, so
each long wagon is fresh among reduced connectors. We transfer this
unconditionally to every original source CUT connector. No hidden
freshness hypothesis is needed. -/
theorem attachedSelectedPicture_supreme_long_wagon_fresh_at_source_cuts
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target : Fin (cyclicOwnerChanges owner))
    (hSupreme : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).HasSupremeAt Wit target) :
    let Z := attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts
    ∃ pieces : Fin (cyclicOwnerChanges owner) →
        TrainSupremePiece CoreEdge (Quotient (U.wagonSetoid μ)),
      Z.PlanValid Wit target pieces ∧
      Z.PlanProducesBigCycle Wit pieces ∧
      (∀ (cut : Fin (cyclicOwnerChanges owner))
        (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ)),
        pieces cut = .long first w second →
        ∀ j : Fin (cyclicOwnerChanges owner),
          K.connector (cyclicOwnerCutIndex owner j) ≠
            Sum.inr (CoreWagon w)) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨pieces, hPlan, hProduces, hFresh⟩ :=
    OrderOneData.BigCycle.freshness_of_hasSupremeAt Wit Z target hSupreme
  refine ⟨pieces, hPlan, hProduces, ?_⟩
  intro cut first second w hp
  exact attachedSelectedPicture_reduced_wagon_fresh_at_all_source_cuts
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts w (hFresh cut first w second hp)

end ActualReducedCutFreshness
end StructuralRamsey.Girth
