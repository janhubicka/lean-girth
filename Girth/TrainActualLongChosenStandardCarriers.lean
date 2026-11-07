import Girth.TrainActualPositiveCutShortPieceLift
import Mathlib.Tactic

/-!
# Path A: actual LongValid physical edge carriers inside chosen standard

A concrete reduced LongValid indexed source is a genuine designated
gluing standard i. Its TWO witness core support edges are members of
the exact copy edge family (Wit).edges (.inl i), so each is the image
of a shared old A-support edge of i. Existing core physical embedding
then places BOTH full physical output edge carriers inside the actual
attached standard i.

This is independent of source run length, original B-label, fresh or
old wagon, and the choice of one- versus two-short source replacement.
No appendix; exact theorem needed for both two-cut nonedge branches.
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


/-- Both REAL physical edges of an actual reduced LongValid belong
entirely to the specified attached standard at the designated
target, with no original designated source label assumption. -/
theorem attachedSelectedPicture_long_piece_carriers_in_standard
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hCuts : 2 ≤ cyclicOwnerChanges owner)
    (target cut : Fin (cyclicOwnerChanges owner)) (i : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).label target = Sum.inl i)
    (first second : CoreEdge) (w : Quotient (U.wagonSetoid μ))
    (hLong : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hCuts).LongValid Wit target cut first w second) :
    (CoreActual first).1 ⊆ copyCarrier (Std i) ∧
    (CoreActual second).1 ⊆ copyCarrier (Std i) := by
  obtain ⟨_x, _y, _hPrev, _hHere, hFirst, hSecond,
    _hne, _hpFirst, _hpSecond, _hx, _hy, _hNoPair⟩ := hLong
  have hFirstOwned : first ∈ (Wit).edges (Sum.inl i) := by
    rw [← hTarget]
    exact hFirst
  have hSecondOwned : second ∈ (Wit).edges (Sum.inl i) := by
    rw [← hTarget]
    exact hSecond
  change first ∈ Set.range (Emb i) at hFirstOwned
  change second ∈ Set.range (Emb i) at hSecondOwned
  obtain ⟨s, hs⟩ := hFirstOwned
  obtain ⟨t, ht⟩ := hSecondOwned
  constructor
  · rw [← hs]
    exact actualSharedCoreEdge_carrier_subset_standard
      A hA C.toRelStructure S R f i s
  · rw [← ht]
    exact actualSharedCoreEdge_carrier_subset_standard
      A hA C.toRelStructure S R f i t

end PositiveCutShortPieceLift
end StructuralRamsey.Girth
