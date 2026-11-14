import Girth.TrainFillingSelectedActualFilledData
import Girth.TrainFillingTemplateConstruction
import Girth.TrainSelectedPictureTwoStandard

set_option Elab.async false

/-!
# True shorter-stage tail system girth in the actual selected H filling

The genuine shorter train witness already proves a full simultaneous
system-girth bound at each positive old cut. For the canonical filling
with old edge family LITERALLY equal to all actual A-support copies
of the shorter stage, its old-edge subtype is the same physical
OldACarrierEdge sort. The actual old selected-parent data is then
the selectedPictureOrderOneData of the stage, not merely a family
of carrier sets.

This is a proposed direct instantiation of the checked full filling
girth transfer. It does NOT assert old equality-cut FullSystemGirthGT
from bottomForest, because that is a separate missing bridge; nor
does it introduce a top-cut system bound. The template is the actual
relational A-support of R, with nontrivial A so its edges have
at least two vertices. The full H edge set and its old cover come
from UniformFillingData.ofSupportCopies, not from hypotheses about
the eventual output.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {C V P X UA Base : Type v}
variable (U : C → PrivateWagonInput V P X)
variable [Nontrivial X] [Nontrivial UA]

/-- For an actual shorter-train stage, all positive old tail
FullSystemGirthGT certificates transfer to the complete filled
selected-parent incidence record with their inherited labels.

The only inputs beyond the true stage are the actual X placement
on each N support edge and the source relational template's
coverage and linearity. Nothing assumes an output H-girth bound. -/
theorem selectedStageActualFilledTailGirth_of_trueStage
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
    (R : RelStructure L X)
    (place : OldACarrierEdge A S.system.toRelStructure → (X ↪ S.Vertex))
    (hRange : ∀ f, Set.range (place f) = f.1)
    (hCovers : ∀ x : X, ∃ a : Embedding A R, x ∈ copyCarrier a)
    (hTemplateLinear : ALinear A R)
    (j : Fin t.length) (hj : 0 < j.val) :
    let H := UniformFillingData.ofSupportCopies A R
      (supportCopies A S.system.toRelStructure) place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        A S.system.toRelStructure S.aLinear)
      hCovers
    (selectedStageActualFilledData U A M T hm hSupport hLinear
      D family allowed S H rfl j.castSucc).FullSystemGirthGT
        (t.get j) := by
  let H : UniformFillingData S.Vertex X :=
    UniformFillingData.ofSupportCopies A R
      (supportCopies A S.system.toRelStructure) place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        A S.system.toRelStructure S.aLinear)
      hCovers
  have hOldBound :
      (H.toTrainFilling.oldCutData
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H rfl)
        (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
          copyCarrier i.1.embedding)
        (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
          {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding})
        j.castSucc).FullSystemGirthGT (t.get j) := by
    change
      (selectedPictureOrderOneData A M D S.system family
        S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
    exact S.tailGirth j hj
  exact selectedStageActualFilledData_fullSystemGirthGT_of_old
    U A M T hm hSupport hLinear D family allowed S H rfl
    j.castSucc (t.get j) hOldBound
    (oldACarrier_edges_inter_subsingleton_of_aLinear
      A R hTemplateLinear)


/-- The genuinely ORDERED shorter-train Ramsey witness supplies the
complete old-cut FullSystemGirthGT certificate at EVERY proper cut,
INCLUDING the old equality cut j=0, through its checked `allCutGirth`
field. No doubled bottom forest and no additional target girth are
needed.

Use the canonical filling whose old edge family is the literal
A-support of the shorter ordered stage. All *restored* positive
system-girth coordinates then inherit the correct, original
shorter-train cutoff values, without introducing a bound at the top.

This is the cutoff-two application of the ORDER assertion, rather
than the weaker FOREST assertion which lacks the j=0 certificate. -/
theorem selectedStageActualFilledAllCuts_of_orderStage
    (A : RelStructure L UA) (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (R : RelStructure L X)
    (place : OldACarrierEdge A S.system.toRelStructure → (X ↪ S.Vertex))
    (hRange : ∀ f, Set.range (place f) = f.1)
    (hCovers : ∀ x : X, ∃ a : Embedding A R, x ∈ copyCarrier a)
    (hTemplateLinear : ALinear A R)
    (j : Fin t.length) :
    let H := UniformFillingData.ofSupportCopies A R
      (supportCopies A S.system.toRelStructure) place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        A S.system.toRelStructure S.aLinear)
      hCovers
    (selectedStageActualFilledData U A M T hm hSupport hLinear
      D family allowed S.toForestTailStage H rfl j.castSucc).FullSystemGirthGT
        (t.get j) := by
  let H : UniformFillingData S.Vertex X :=
    UniformFillingData.ofSupportCopies A R
      (supportCopies A S.system.toRelStructure) place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        A S.system.toRelStructure S.aLinear)
      hCovers
  have hOldBound :
      (H.toTrainFilling.oldCutData
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S.toForestTailStage H rfl)
        (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
          copyCarrier i.1.embedding)
        (fun i : {b : DesignatedCopy M D S.system family // b ∈ S.selected} =>
          {f : H.OldEdge | f.1 ⊆ copyCarrier i.1.embedding})
        j.castSucc).FullSystemGirthGT (t.get j) := by
    change
      (selectedPictureOrderOneData A M D S.system family
        S.selected S.train j.castSucc).FullSystemGirthGT (t.get j)
    exact S.allCutGirth j
  exact selectedStageActualFilledData_fullSystemGirthGT_of_old
    U A M T hm hSupport hLinear D family allowed
    S.toForestTailStage H rfl
    j.castSucc (t.get j) hOldBound
    (oldACarrier_edges_inter_subsingleton_of_aLinear
      A R hTemplateLinear)


end StructuralRamsey.Girth.IndexedPrivateChoice
