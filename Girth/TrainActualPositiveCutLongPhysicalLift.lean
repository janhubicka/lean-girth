import Girth.TrainActualCoreNoNewPair
import Girth.TrainOneFreshLongPhysical
import Girth.TrainActualSupremeCutBoundarySupport

/-!
# A reduced actual LongValid piece lifts to physical output long geometry

We transport the two reduced cut connectors through the checked
actual core vertex/wagon maps, and map BOTH witness core support edges
to their genuine physical output A-edges.

The source LongValid nonedge condition transfers to the WHOLE output
under explicit active A-strongness: an ambient output pair edge through
two distinct embedded core vertices would have a genuine source
core-edge preimage. No original designated B-label has been chosen.
Thus the result is PhysicalLongGeometry, NOT a spurious source-indexed
LongValid proof.

The boundary cut-index equalities, actual strong gluing input and
existence of the reduced long piece remain explicit. Freshness of the
wagon, and strict minimum owner-cut descent after insertion, are
separate geometric steps. Circulation only; no appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualPositiveCutLongPhysicalLift

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

/-- LongValid at a genuine reduced positive cut has exactly the
physical data for an arbitrary one-long output insertion, with NO
old source designated-label membership. Two old source boundary
indices are specified; their equality is a separate segmentation
fact, while the output nonpair condition is PROVED by A-strongness. -/
theorem attachedSelectedPicture_reduced_long_piece_physical_output
    {n : ℕ} (K : (Out).BigCycle n)
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
      (trainCyclicPred cut) = trainCyclicPred pos) :
    K.PhysicalLongGeometry Out pos
      (CoreActual first) (CoreWagon w) (CoreActual second) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
  obtain ⟨x, y, hLeft, hRight, _hMemFirst, _hMemSecond,
    hNe, hParentFirst, hParentSecond, hx, hy, hNoPair⟩ := hLong
  have hMap (j : Fin (cyclicOwnerChanges owner)) :
      Sum.map CoreEmb CoreWagon (Z.connector j) =
        K.connector (cyclicOwnerCutIndex owner j) := by
    change Sum.map CoreEmb CoreWagon
      (attachedSelectedPicture_cutConnector
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed j) =
        K.connector (cyclicOwnerCutIndex owner j)
    exact attachedSelectedPicture_cutConnector_eq
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed j
  have hAtPrev : K.connector (trainCyclicPred pos) =
      Sum.inl (CoreEmb x) := by
    have h := hMap (trainCyclicPred cut)
    rw [hLeft, hPrevious] at h
    exact h.symm
  have hAtHere : K.connector pos = Sum.inl (CoreEmb y) := by
    have h := hMap cut
    rw [hRight, hThis] at h
    exact h.symm
  have hActualNe : CoreActual first ≠ CoreActual second := by
    intro heq
    have hOriginal :=
      (actualAPictureEdgeEquiv A hA C.toRelStructure S R f).injective heq
    have hEq : first = second := by
      simpa [physicalCoreEdge] using hOriginal
    exact hNe hEq
  have hParentE : (Out).parent (CoreActual first) = CoreWagon w := by
    change CoreWagon ((Wit).parent first) = CoreWagon w
    exact congrArg CoreWagon hParentFirst
  have hParentF : (Out).parent (CoreActual second) = CoreWagon w := by
    change CoreWagon ((Wit).parent second) = CoreWagon w
    exact congrArg CoreWagon hParentSecond
  have hEdgeX : CoreEmb x ∈ (CoreActual first).1 := by
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f first]
    exact ⟨x, hx, rfl⟩
  have hEdgeY : CoreEmb y ∈ (CoreActual second).1 := by
    rw [actualAPictureEdgeEquiv_core_carrier
      A hA C.toRelStructure S R f second]
    exact ⟨y, hy, rfl⟩
  have hXY : x ≠ y := by
    intro hEq
    subst y
    exact hNoPair ⟨first, hx, hx⟩
  have hNoActualPair : ¬ (Out).PairEdge (CoreEmb x) (CoreEmb y) :=
    attachment_core_nonpair_preserved_of_aStrong
      A hA C.toRelStructure S R f hActive x y hXY hNoPair
  exact ⟨CoreEmb x, CoreEmb y, hAtPrev, hAtHere,
    hActualNe, hParentE, hParentF, hEdgeX, hEdgeY, hNoActualPair⟩

end ActualPositiveCutLongPhysicalLift
end StructuralRamsey.Girth
