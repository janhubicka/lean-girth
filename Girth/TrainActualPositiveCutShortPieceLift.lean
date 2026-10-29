import Girth.TrainActualSupremeCutBoundarySupport
import Girth.TrainActualSharedCoreEdgeStandard

/-!
# Track A: transport one REAL reduced short piece to the original boundaries

The selected cut-indexed witness uses core A-support edges and quotient
wagon connectors. A ShortValid witness edge at a cut represents an
actual support edge incident with BOTH original connectors when those
two cut positions are the boundaries of a singleton source segment.

This lemma does not assume the reduced supreme gluing-copy label is an
original designated B-label. It also does not assert the existence of
a reduced short piece or the singleton boundary-index equalities:
those are the still-open geometric extraction step.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section PositiveCutShortPieceLift

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
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
    (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- A short piece of the actual cut-indexed witness is a physical
edge incident with both original connectors of the corresponding
single-occurrence segment. The two source cut-index equalities are
explicit and can be established independently from the run geometry. -/
theorem attachedSelectedPicture_cut_short_piece_incident_lift
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner))
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).ShortValid (Wit) target cut b)
    (pos : Fin n)
    (hThis : cyclicOwnerCutIndex owner cut = pos)
    (hPrevious : cyclicOwnerCutIndex owner
      (trainCyclicPred cut) = trainCyclicPred pos) :
    (Out).Incident (Sum.inr (CoreActual b))
      (K.connector (trainCyclicPred pos)) ∧
    (Out).Incident (Sum.inr (CoreActual b))
      (K.connector pos) := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed hCuts
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
  have hLeft := attachedSelectedPicture_core_edge_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    b (Z.connector (trainCyclicPred cut)) hShort.2.1
  have hRight := attachedSelectedPicture_core_edge_incident_lift
    A hA B D C family selected e R f T U hShared hRel μ
    b (Z.connector cut) hShort.2.2
  rw [hMap (trainCyclicPred cut), hPrevious] at hLeft
  rw [hMap cut, hThis] at hRight
  exact ⟨hLeft, hRight⟩

/-- When the chosen reduced witness label is a gluing copy i,
the physical edge in a ShortValid piece genuinely comes from
one of i's shared support edges. This is not a designated source
B-label, and no unnecessary old copy identity is asserted. -/
theorem attachedSelectedPicture_cut_short_piece_has_shared_source
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).ShortValid (Wit) target cut b) :
    ∃ s : Shared, Emb i s = b := by
  have hb : b ∈ (Wit).edges (Sum.inl i) := by
    rw [← hTarget]
    exact hShort.1
  change b ∈ Set.range (Emb i) at hb
  exact hb

/-- An actual witness ShortValid piece whose chosen label is the
standard i provides a physically contained output edge; this
does not yet assert the piece is at a singleton source occurrence. -/
theorem attachedSelectedPicture_cut_short_piece_carrier_in_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (b : CoreEdge)
    (hShort : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).ShortValid (Wit) target cut b) :
    (CoreActual b).1 ⊆ copyCarrier (Std i) := by
  obtain ⟨s, hs⟩ :=
    attachedSelectedPicture_cut_short_piece_has_shared_source
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts target cut i hTarget b hShort
  rw [← hs]
  exact actualSharedCoreEdge_carrier_subset_standard
    A hA C.toRelStructure S R f i s

end PositiveCutShortPieceLift
end StructuralRamsey.Girth
