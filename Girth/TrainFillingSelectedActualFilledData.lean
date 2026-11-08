import Girth.TrainFillingSelectedActualCopyEdges
import Girth.TrainFillingSelectedActualRestoredWagons

set_option Elab.async false

/-!
# The actual complete filled incidence system of selected M parents

For a fixed old proper cut nu the shorter-train witness has genuine
selected labelled M-copies.  Build the full OLD-parent incidence model
inside the constructed filling H, keeping:
* every ambient filled H physical edge;
* the complete selected M vertex carrier as each parent's copyCarrier;
* ALL filled physical edges whose real old cover lies in the selected
  M old-support carrier;
* the ACTUAL restored quotient wagon labels at nu.succ.

The resulting copy-edge family is not independently declared equal
to the image of the heterogeneous G0; that equality is a THEOREM of
the selected M-copy's checked A-strongness, proved in the separate
selected old/fill copy-edge range bridge.

This is precisely the old-parent input representation to which the
already checked full-system filling and scattering lemmas apply.
It does not assert that it has full system girth or a final Ramsey
arrow merely by being defined.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X UA Base : Type v} {L : RelLanguage.{u}}
variable (U : C → PrivateWagonInput V P X)
variable [Nontrivial X]

/-- The full ambient filled incidence record, with the genuine selected
shorter-train copy subtype as its designated parent labels and the
actual inherited quotient train on ALL physical H edges. -/
noncomputable def selectedStageActualFilledData
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (ν : Fin (t.length + 1)) :
    OrderOneData S.Vertex H.toTrainFilling.NewEdge
      {b : DesignatedCopy M D S.system family // b ∈ S.selected}
      (Quotient (((H.toTrainFilling).inheritedTrain
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H hOld)).wagonSetoid ν.succ)) where
  edgeCarrier := fun edge => edge.1
  copyCarrier := fun i => copyCarrier i.1.embedding
  copyEdges := fun i =>
    {e : H.toTrainFilling.NewEdge |
      H.toTrainFilling.cover e ∈
        {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding}}
  parent := Quotient.mk _

/-- The chosen parent vertex carrier is literally the image of its
selected M embedding, with no additional global compatibility input. -/
@[simp] theorem selectedStageActualFilledData_copyCarrier
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (ν : Fin (t.length + 1))
    (i : {b : DesignatedCopy M D S.system family // b ∈ S.selected}) :
    (selectedStageActualFilledData U A M T hm hSupport hLinear
      D family allowed S H hOld ν).copyCarrier i =
      Set.range i.1.embedding.toFunctionEmbedding := rfl

/-- The natural FULL selected filled copy-edge set equals the image of
the constructed physical G0→H edge embedding over that parent's
entire heterogeneous first-wagon family, by selected A-strongness
and the literal old filling cover. -/
theorem selectedStageActualFilledData_copyEdges_eq_range
    [Nontrivial UA]
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (ν : Fin (t.length + 1))
    (i : {b : DesignatedCopy M D S.system family // b ∈ S.selected}) :
    (selectedStageActualFilledData U A M T hm hSupport hLinear
      D family allowed S H hOld ν).copyEdges i =
    Set.range (selectedIndexedFilledEdgeEmbedding U H hTemplate
      (selectedStageActualOldEdgeEmbedding U A M T hm hSupport
        hLinear D family allowed S i.1 H hOld)) := by
  exact selectedStageActualFilledCopyEdges_eq_range U A M T hm
    hSupport hLinear D family allowed S i.1 i.2 H hOld hTemplate


/-- This is exactly the checked inherited quotient-cut incidence record.
The ambient H edge family, every selected designated copy, every copied
physical edge, and the literal restored wagon parent are identical.

The identification is definitional, not an image approximation or a
quotient of repeated carrier sets. -/
theorem selectedStageActualFilledData_eq_inheritedCutData
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (ν : Fin (t.length + 1)) :
    selectedStageActualFilledData U A M T hm hSupport hLinear
      D family allowed S H hOld ν =
    H.toTrainFilling.inheritedCutData
      (selectedStageActualOldTrain U A M T hm hSupport hLinear
        D family allowed S H hOld)
      (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
        copyCarrier i.1.embedding)
      (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
        {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding}) ν := rfl

/-- The genuine selected filled incidence record inherits the FULL
simultaneous A2/A3 system-girth bound from its old parent incidence
record at one proper cut. This uses the checked filling theorem, not
a separate girth assumption on the output H.

The old full bound remains a genuine input from the recursive
shorter-train stage; connecting it to that stage's tail certificate
is a separate, explicit obligation. The only extra geometric input
is linearity of different local template edges in one filling fibre. -/
theorem selectedStageActualFilledData_fullSystemGirthGT_of_old
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (ν : Fin (t.length + 1)) (g : ℕ)
    (hOldBound :
      (H.toTrainFilling.oldCutData
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H hOld)
        (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
          copyCarrier i.1.embedding)
        (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
          {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding}) ν).FullSystemGirthGT g)
    (hTemplateLinear : ∀ a b : H.TemplateEdge, a ≠ b →
      (a.1 ∩ b.1).Subsingleton) :
    (selectedStageActualFilledData U A M T hm hSupport hLinear
      D family allowed S H hOld ν).FullSystemGirthGT g := by
  rw [selectedStageActualFilledData_eq_inheritedCutData
    U A M T hm hSupport hLinear D family allowed S H hOld ν]
  exact H.toTrainFilling.inheritedCutData_fullSystemGirthGT_of_fibreLinearity
    (selectedStageActualOldTrain U A M T hm hSupport hLinear
      D family allowed S H hOld)
    (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
      copyCarrier i.1.embedding)
    (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
      {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding})
    ν hOldBound (H.fibre_linear hTemplateLinear)


end StructuralRamsey.Girth.IndexedPrivateChoice
