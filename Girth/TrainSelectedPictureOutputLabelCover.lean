import Girth.TrainSelectedPictureOutputIncidence

/-!
# Circulation: every actual output label has a concrete source

To define the witness reduct, one must first classify every occurrence
of the actual selected-picture cycle. A designated occurrence is
literally an indexed selected old copy. Every physical A-support edge
is the image of either a genuine witness-core edge or an indexed old
standard edge: the physical edge pushout is exhaustive.

The second alternative may have multiple standard representations for
a SHARED edge, so this theorem does NOT choose a unique owner or infer
one merely from geometrical containment. It provides the explicit
source representation needed before choosing minimum segments.

No cycle reduction, cyclic index system, acceptability or A2/A3
property is asserted. No appendix.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section SelectedOutputLabelCover

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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Label" => Selected ⊕ OldEdge
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Eqv" => actualAPictureEdgeEquiv
  A hA C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  Eqv (physicalCoreEdge
    (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "StdEdge" => (fun (i : I) (a : OldEdge) =>
  Eqv (physicalStandardEdge
    (sharedOldACarrierInclusion A C.toRelStructure S)
    (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) i a))

/-- Every literal selected-picture output occurrence has one of the
two source types required for witness segmentation. The source edge
classification is exhaustive by the ACTUAL physical edge equivalence.
No uniqueness of standard owners is claimed. -/
theorem attachedSelectedPicture_outputLabel_covered
    (a : (I × Selected) ⊕ ActualEdge) :
    (∃ (i : I) (old : Label), a = LabelMap i old) ∨
    (∃ b : CoreEdge, a = Sum.inr (CoreActual b)) := by
  cases a with
  | inl iq =>
      exact Or.inl ⟨iq.1, .inl iq.2, rfl⟩
  | inr edge =>
      let pre := (Eqv).symm edge
      rcases physicalPictureEdge_covered
        (sharedOldACarrierInclusion A C.toRelStructure S)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f) pre
        with ⟨b, hb⟩ | ⟨i, old, hOld⟩
      · right
        refine ⟨b, ?_⟩
        have hEdge : edge = CoreActual b := by
          have h := congrArg Eqv hb
          simpa [pre, CoreActual] using h
        exact congrArg Sum.inr hEdge
      · left
        refine ⟨i, .inr old, ?_⟩
        change Sum.inr edge = Sum.inr (StdEdge i old)
        have hEdge : edge = StdEdge i old := by
          have h := congrArg Eqv hOld
          simpa [pre, StdEdge] using h
        exact congrArg Sum.inr hEdge

/-- Apply the exhaustive source-label classification to EVERY
occurrence of a genuine BigCycle; the classification by itself
does not assert a legal witness reduct. -/
theorem attachedSelectedPicture_cycle_every_label_has_source
    {n : ℕ} (K : (Out).BigCycle n) (k : Fin n) :
    (∃ (i : I) (old : Label),
      K.label k = LabelMap i old) ∨
    (∃ b : CoreEdge,
      K.label k = Sum.inr (CoreActual b)) :=
  attachedSelectedPicture_outputLabel_covered
    A hA B D C family selected e R f (K.label k)

end SelectedOutputLabelCover

end StructuralRamsey.Girth
