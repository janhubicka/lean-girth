import Girth.TrainCyclicExpandedKeepIff
import Girth.TrainActualPlanKeptRunOwner
import Mathlib.Tactic

/-!
# Path A: source-expanded kept occurrences belong to the chosen standard

For a FIXED genuine PlanValid reduced witness and its designated
standard target i, expand that same plan to original source positions
using the verified cyclic run index. The expanded plan keeps a source
position only when its reduced run is kept; PlanValid then forces the
original geometric owner of that occurrence to be i.

No identification between a physical designated B-copy label and its
geometric standard owner is made. This is exactly hKeep in the already
checked one-pass standard-transfer theorem.

It does not prove source local incidence, long A2 geometry, wagon
freshness, or the global supreme transfer. Circulation only.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualSourceExpandedKeepOwner

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

/-- For ANY specified valid reduced supreme plan, every original
occurrence that is kept by the literal expanded source plan has an
actual GEOMETRIC owner equal to the chosen standard i. Thus the
expanded plan satisfies the hKeep premise of the existing global
standard-transfer theorem. -/
theorem attachedSelectedPicture_expanded_plan_keep_owned_by_target
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
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
    ∀ pos : Fin n,
      cyclicExpandReducedPieces owner (by omega) pieces
        CoreActual CoreWagon pos = .keep →
      owner pos = Sum.inl i := by
  intro pos hKeep
  have hReducedKeep :
      pieces (cyclicOwnerRunIndex owner (by omega) pos) = .keep :=
    (cyclicExpandReducedPieces_keep_iff
      owner (by omega) pieces CoreActual CoreWagon pos).mp hKeep
  exact attachedSelectedPicture_plan_keep_original_owner
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts target i hTarget
    pieces hPlan pos hReducedKeep

end ActualSourceExpandedKeepOwner
end StructuralRamsey.Girth
