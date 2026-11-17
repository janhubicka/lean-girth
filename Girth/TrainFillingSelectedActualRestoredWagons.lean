import Girth.TrainFillingSelectedActualHOldTrain
import Girth.TrainFillingIndexedSelectedPhysicalMap
import Girth.TrainFillingIndexedProperWagonReconstruction

set_option Elab.async false

/-!
# Actual restored train wagons from a genuinely selected M-copy

The cutoff-two shortened-train stage has a selected M-copy b, carrying
the full selected train relation by targetRestriction. The checked
literal old-H edge map and its old train have already been constructed
from b, and its proper-cut relation is a theorem (not an input).

The actual filled H train at the inherited ν.succ cut pulls the old
N relation back along the cover of each complete filled edge.
Use the checked indexed physical cover equality to transport both
directions of the relation. Equality of genuine tagged G0 μ-wagon
names is therefore precisely equality of actual restored quotient
wagons. No independent parent-faithfulness premise, target quotient
surjectivity or candidate wagon map is supplied.

Construct the full source proper-wagon injection from the equivalence
using the existing checked representative construction. This closes
the selected-stage/quotient representation bridge conditionally on
the genuine selected stage and nonempty local template edge family.
The global system-girth/scattering and Ramsey arrow remain separate.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X UA Base : Type v} {L : RelLanguage.{u}}
variable (U : C → PrivateWagonInput V P X)
variable [Nontrivial X]

/-- Literal reflection of the ACTUAL restored H quotient-wagon
equality, including all complete filled G0 physical edge occurrences,
from the genuine selected shorter-train stage's targetRestriction. -/
theorem selectedStageRestoredParent_iff
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
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (a d : Edge U) :
    properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) a =
      properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) d ↔
    (Quotient.mk
      (((H.toTrainFilling).inheritedTrain
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H hOld)).wagonSetoid ν.succ)
        (selectedIndexedFilledEdgeEmbedding U H hTemplate
          (selectedStageActualOldEdgeEmbedding U A M T hm hSupport
            hLinear D family allowed S b H hOld) a)) =
    (Quotient.mk
      (((H.toTrainFilling).inheritedTrain
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H hOld)).wagonSetoid ν.succ)
        (selectedIndexedFilledEdgeEmbedding U H hTemplate
          (selectedStageActualOldEdgeEmbedding U A M T hm hSupport
            hLinear D family allowed S b H hOld) d)) := by
  let β := selectedStageActualOldEdgeEmbedding U A M T hm
    hSupport hLinear D family allowed S b H hOld
  let S_old := selectedStageActualOldTrain U A M T hm hSupport hLinear
    D family allowed S H hOld
  let f := selectedIndexedFilledEdgeEmbedding U H hTemplate β
  have hSource :
      properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) a =
        properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) d ↔
      (contractedChoiceTrain U T hm).rel ν (a.1, a.2.1) (d.1, d.2.1) := by
    change contractedProperParent U T ν (a.1, a.2.1) =
      contractedProperParent U T ν (d.1, d.2.1) ↔ _
    exact contractedProperParent_eq_iff_rel U T hm ν hProper
      (a.1, a.2.1) (d.1, d.2.1)
  have hStage :
      (contractedChoiceTrain U T hm).rel ν (a.1, a.2.1) (d.1, d.2.1) ↔
      S_old.rel ν (β (a.1, a.2.1)) (β (d.1, d.2.1)) := by
    exact selectedStageActualOldTrain_rel_iff U A M T hm hSupport
      hLinear D family allowed S b hb H hOld ν
      (a.1, a.2.1) (d.1, d.2.1)
  have hRestore :
      S_old.rel ν (β (a.1, a.2.1)) (β (d.1, d.2.1)) ↔
        Quotient.mk ((H.toTrainFilling.inheritedTrain S_old).wagonSetoid ν.succ)
          (f a) =
        Quotient.mk ((H.toTrainFilling.inheritedTrain S_old).wagonSetoid ν.succ)
          (f d) := by
    constructor
    · intro hab
      apply Quotient.sound
      apply (H.toTrainFilling.inheritedTrain_rel_succ S_old ν (f a) (f d)).mpr
      simpa only [selectedIndexedFilledEdgeEmbedding_cover] using hab
    · intro heq
      have hrel :
          (H.toTrainFilling.inheritedTrain S_old).rel ν.succ (f a) (f d) :=
        Quotient.exact heq
      have hh := (H.toTrainFilling.inheritedTrain_rel_succ
        S_old ν (f a) (f d)).mp hrel
      simpa only [selectedIndexedFilledEdgeEmbedding_cover] using hh
  exact hSource.trans (hStage.trans hRestore)

/-- Every tagged proper wagon has an actual H restored-quotient
representative, and reflection makes its image injective. The map
is constructed on the genuine selected M-copy; source wagon
surjectivity is simply that every Quotient label has a representative.
No ambient quotient-wagon surjectivity is used. -/
noncomputable def selectedStageActualRestoredWagonEmbedding
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
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge) :
    ProperWagon (Q := Quotient (T.wagonSetoid ν)) U ↪
      Quotient (((H.toTrainFilling).inheritedTrain
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H hOld)).wagonSetoid ν.succ) := by
  let β := selectedStageActualOldEdgeEmbedding U A M T hm
    hSupport hLinear D family allowed S b H hOld
  let S_old := selectedStageActualOldTrain U A M T hm hSupport hLinear
    D family allowed S H hOld
  have hParent : Function.Surjective
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p) := by
    intro q
    induction q using Quotient.inductionOn with
    | h p => exact ⟨p, rfl⟩
  exact reconstructedProperWagonEmbedding U
    (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
    (selectedIndexedFilledEdgeEmbedding U H hTemplate β)
    (fun e : H.toTrainFilling.NewEdge =>
      Quotient.mk (((H.toTrainFilling).inheritedTrain S_old).wagonSetoid ν.succ) e)
    hParent hLocal
    (selectedStageRestoredParent_iff U A M T hm hSupport hLinear
      D family allowed S b hb H hOld hTemplate ν hProper)

/-- The actual selected restored wagon embedding commutes with
genuine G0 physical edge parents at every nonterminal cut. -/
theorem selectedStageActualRestoredWagonEmbedding_parent
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
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge) (a : Edge U) :
    selectedStageActualRestoredWagonEmbedding U A M T hm
      hSupport hLinear D family allowed S b hb H hOld hTemplate
      ν hProper hLocal
      (properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) a) =
    Quotient.mk
      (((H.toTrainFilling).inheritedTrain
        (selectedStageActualOldTrain U A M T hm hSupport hLinear
          D family allowed S H hOld)).wagonSetoid ν.succ)
      (selectedIndexedFilledEdgeEmbedding U H hTemplate
        (selectedStageActualOldEdgeEmbedding U A M T hm hSupport hLinear
          D family allowed S b H hOld) a) := by
  let β := selectedStageActualOldEdgeEmbedding U A M T hm
    hSupport hLinear D family allowed S b H hOld
  let S_old := selectedStageActualOldTrain U A M T hm hSupport hLinear
    D family allowed S H hOld
  have hParent : Function.Surjective
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p) := by
    intro q
    induction q using Quotient.inductionOn with
    | h p => exact ⟨p, rfl⟩
  exact reconstructedProperWagonEmbedding_parent U
    (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
    (selectedIndexedFilledEdgeEmbedding U H hTemplate β)
    (fun e : H.toTrainFilling.NewEdge =>
      Quotient.mk (((H.toTrainFilling).inheritedTrain S_old).wagonSetoid ν.succ) e)
    hParent hLocal
    (selectedStageRestoredParent_iff U A M T hm hSupport hLinear
      D family allowed S b hb H hOld hTemplate ν hProper) a

end StructuralRamsey.Girth.IndexedPrivateChoice
