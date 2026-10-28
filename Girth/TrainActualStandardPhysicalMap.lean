import Girth.TrainSupremePlanTransport
import Girth.TrainActualStandardNoNewPair

/-!
# The actual one-standard picture is a literal physical incidence map

This is the concrete bridge between the GENERIC global supreme-plan
transport and the genuine picture-step attachment.

All four maps are real injections:
* old vertices via the actual attachment standard embedding;
* old A-support edges via their genuine standard physical support
  carrier sets (including shared edges realized in the core);
* old designated labels via the tagged SAME-standard selected label;
* old wagon classes via exact generated train restriction.

All labelled incidences, source-edge membership and edge-parent
classes are preserved. There are no newly created ambient pair edges
between two different standard vertices provided the attached
standard is A-strong. This is supplied by the old active-subsystem
A-strongness and the A-strongness of EACH core gluing image.

No assumption that a relational embedding is automatically
A-strong is made. A subsequent module will apply this map to
genuine zero-cut cycles and lift entire simultaneous supreme plans.
No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualStandardPhysicalMap

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
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdEdge" => fun (i : I) (old : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge
      (sharedOldACarrierInclusion A C.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) i old)
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- The actual old standard is a FULL literal physical map into the
attached picture. The only strongness premises are exactly those
needed by the pre-existing free-attachment strongness theorem:
the old gluing subsystem, and every core gluing-image. -/
noncomputable def attachedSelectedPicture_standard_physicalMap
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (i : I) :
    OrderOneData.LiteralPhysicalMap (Old) (Out) := by
  let hStdStrong : AStrong A
      (RelStructure.Attachment.attach C.toRelStructure S R f)
      (copyCarrier (Std i)) :=
    attachment_copy_aStrong
      C.toRelStructure S R f hA hOldStrong hCoreStrong i
  have hMappedLabel (a : Selected ⊕ OldEdge) :
      Sum.map (fun q : Selected => (i, q)) (StdEdge i) a =
        LabelMap i a := by
    cases a <;> rfl
  refine {
    vertex := (Std i).toFunctionEmbedding
    edge := ⟨StdEdge i,
      attachedSelectedPicture_standard_edge_injective
        A hA D C e R f T U hRel i⟩
    designated := ⟨(fun q : Selected => (i, q)), ?_⟩
    wagon := StdWagon i
    incident := ?_
    source_edge := ?_
    parent := ?_
    no_new_pair := ?_
  }
  · intro a b h
    exact congrArg Prod.snd h
  · intro a q h
    cases q with
    | inl x =>
        change x ∈ (Old).carrier a at h
        have hPhysical : Std i x ∈ (Out).carrier (LabelMap i a) := by
          rw [attachedSelectedPicture_carrier
            A hA B D C family selected e R f T U hShared μ i a]
          exact ⟨x, h, rfl⟩
        change Std i x ∈ (Out).carrier
          (Sum.map (fun q : Selected => (i, q)) (StdEdge i) a)
        exact Eq.mp
          (congrArg (fun lab => Std i x ∈ (Out).carrier lab)
            (hMappedLabel a).symm) hPhysical
    | inr p =>
        change (Old).Meets a p at h
        obtain ⟨old, he, hp⟩ := h
        change (Out).Meets
          (Sum.map (fun q : Selected => (i, q)) (StdEdge i) a)
          (StdWagon i p)
        have hPhysical : (Out).Meets (LabelMap i a) (StdWagon i p) := by
          refine ⟨StdEdge i old, ?_, ?_⟩
          · exact attachedSelectedPicture_standard_edge_membership_lift
              A hA B D C family selected e R f T U hShared hRel μ
              i a old he
          · change Quotient.mk ((Train).wagonSetoid μ) (StdEdge i old) =
              StdWagon i p
            calc
              _ = StdWagon i (Quotient.mk (T.wagonSetoid μ) old) :=
                (generatedActualASupportTrain_standardWagonEmbedding_mk
                  A hA C.toRelStructure S R f T U hRel hShared μ i old).symm
              _ = StdWagon i p := congrArg (StdWagon i) hp
        exact Eq.mp
          (congrArg (fun lab => (Out).Meets lab (StdWagon i p))
            (hMappedLabel a).symm) hPhysical
  · intro a old he
    change StdEdge i old ∈ (Out).edges
      (Sum.map (fun q : Selected => (i, q)) (StdEdge i) a)
    have hPhysical : StdEdge i old ∈
        (Out).edges (LabelMap i a) :=
      attachedSelectedPicture_standard_edge_membership_lift
        A hA B D C family selected e R f T U hShared hRel μ
        i a old he
    exact Eq.mp
      (congrArg (fun lab => StdEdge i old ∈ (Out).edges lab)
        (hMappedLabel a).symm) hPhysical
  · intro old
    exact generatedActualASupportTrain_standardWagonEmbedding_mk
      A hA C.toRelStructure S R f T U hRel hShared μ i old |>.symm
  · intro x y hxy hPair
    exact attachedSelectedPicture_standard_pairEdge_back_of_aStrong
      A hA B D C family selected e R f T U hShared hRel μ
      i hStdStrong x y hxy hPair

end ActualStandardPhysicalMap
end StructuralRamsey.Girth
