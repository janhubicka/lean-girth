import Girth.TrainCoreWagonEmbedding
import Girth.TrainSelectedCycleGeometricWagon

/-!
# An actual standard's old wagon classes embed in the generated output

Exact restriction of the generated train relation to genuine old
standard A-support edges implies an injective old-wagon -> output-wagon
map. No wagon is identified merely because its physical carrier
happens to agree with another wagon's carrier.

Moreover, if a physical output label is geometrically contained in
one attached standard, every output wagon it meets lies IN THE IMAGE
of that standard's injected old wagon map. This holds for foreign
designated output labels too, because physical incidence edges are
pulled back without changing their designated-label provenance.

Together with the separate two-support-edge label-identity theorem,
these are the quotient ingredients of a zero-cut old-cycle pullback.
The full cycle constructor/acceptability transfer remains separate.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section StandardWagonMap

variable {L : RelLanguage.{u}} {UA Old Core I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L Old) (S : Set Old)
variable (D : RelStructure L Core)
variable (f : I → RelStructure.Embedding (B.induce S) D)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A B) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A D) m)
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A B S),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A B S D f j p)
      (sharedOldACarrierCoreEmbedding A B S D f j q))
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A B S))
variable (μ : Fin (m + 1))

local notation "Train" => generatedActualASupportTrain
  A hA B S D f T U hShared
local notation "StdEdge" => fun (i : I) (a : OldACarrierEdge A B) =>
  actualAPictureEdgeEquiv A hA B S D f
    (physicalStandardEdge (sharedOldACarrierInclusion A B S)
      (sharedOldACarrierCoreEmbedding A B S D f) i a)

/-- The old standard wagon partition is injected into the ACTUAL
output wagon partition at every train coordinate. The complete
reflection/preservation equivalence is used, not carrier equality. -/
noncomputable def generatedActualASupportTrain_standardWagonEmbedding
    (i : I) :
    Quotient (T.wagonSetoid μ) ↪ Quotient (Train.wagonSetoid μ) :=
  T.wagonEmbeddingOfRelationIff Train μ (StdEdge i)
    (fun a b => generatedActualASupportTrain_restrict_standard
      A hA B S D f T U hRel hShared μ i a b)

/-- A genuine standard A-edge maps into exactly its physical output
wagon, by equality in the output quotient of actual A-support edges. -/
theorem generatedActualASupportTrain_standardWagonEmbedding_mk
    (i : I) (a : OldACarrierEdge A B) :
    generatedActualASupportTrain_standardWagonEmbedding
      A hA B S D f T U hRel hShared μ i
      (Quotient.mk (T.wagonSetoid μ) a) =
    Quotient.mk (Train.wagonSetoid μ) (StdEdge i a) := rfl

end StandardWagonMap

section UsedStandardWagon

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" =>
  OldACarrierEdge A (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdEdge" => fun (i : I) (a : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge (sharedOldACarrierInclusion A C.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) i a)

/-- A physical wagon used by ANY geometrically standard-contained
output label is exactly the image of a genuine old wagon from that
standard. No literal source label or old edge representative is
assumed; it is constructed from the actual physical incidence. -/
theorem attachedSelectedPicture_geometric_used_wagon_in_standard_range
    (i : I)
    (a : (I × Selected) ⊕ ActualEdge)
    (W : Quotient (Train.wagonSetoid μ))
    (hContained : (Out).carrier a ⊆ copyCarrier (Std i))
    (hMeets : (Out).Meets a W) :
    ∃ p : Quotient (T.wagonSetoid μ),
      generatedActualASupportTrain_standardWagonEmbedding
        A hA C.toRelStructure S R f T U hRel hShared μ i p = W := by
  obtain ⟨old, hOutput⟩ :=
    attachedSelectedPicture_geometric_wagon_source
      A hA B D C family selected e R f T U hShared μ
      i a W hContained hMeets
  refine ⟨Quotient.mk (T.wagonSetoid μ) old, ?_⟩
  rw [generatedActualASupportTrain_standardWagonEmbedding_mk]
  exact hOutput

end UsedStandardWagon
end StructuralRamsey.Girth
