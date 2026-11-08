import Girth.TrainFillingIndexedActualMPhysicalTrain
import Girth.TrainFillingIndexedContractedCarriers

set_option Elab.async false

/-!
# Genuine selected M-copy to the ACTUAL old H-edge train

The complete contracted M is now a relational source whose A-support
edges are exactly the choice-indexed first wagons.  The selected
shorter-train stage carries its genuine selected M-copy, with both
physical edge transport and all-level relation reflection proved from
its targetRestriction field.

The full filling H has its old edge family equal to the complete
A-support family of the selected stage's ambient N.  Reinterpret
H.OldEdge in that actual subtype, construct the selected old-edge map
from the selected *vertex* embedding, and prove that this map is
LITERALLY the selected ForestTailStage physical edge map.

The resulting train relation equivalence on H.OldEdge is a theorem
of the genuine selected stage, not a new faithful-parent assumption.
The remaining next step is to compose with restored H quotient
transport and the global parentwise scattering construction.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {C V P X UA Base : Type v} {L : RelLanguage.{u}}
variable (U : C → PrivateWagonInput V P X)
variable [Nontrivial X]

/-- An old H-edge is exactly an ambient relational A-support edge
when those COMPLETE edge families are equal. This changes only the
subtype proof; the actual carrier set is unchanged. -/
def oldSupportEdgeEmbedding
    {W : Type v}
    (A : RelStructure L UA) (N : RelStructure L W)
    (H : UniformFillingData W X)
    (hOld : H.oldEdges = supportCopies A N) :
    H.OldEdge ↪ OldACarrierEdge A N where
  toFun e := ⟨e.1, by
    rw [← hOld]
    exact e.2⟩
  inj' := by
    intro e f h
    exact Subtype.ext (congrArg Subtype.val h)

@[simp] theorem oldSupportEdgeEmbedding_carrier
    {W : Type v} (A : RelStructure L UA) (N : RelStructure L W)
    (H : UniformFillingData W X)
    (hOld : H.oldEdges = supportCopies A N) (e : H.OldEdge) :
    (oldSupportEdgeEmbedding A N H hOld e).1 = e.1 := rfl

/-- The genuine selected b:M→N constructs the physical H old-edge
map on EVERY complete contracted first wagon. No physical image map
and no membership of the selected carrier in H is independently
postulated. Membership is obtained by composing real relational
A-support embeddings and the actual old H-support equality. -/
noncomputable def selectedStageActualOldEdgeEmbedding
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
    (b : DesignatedCopy M D S.system family)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    (C × P) ↪ H.OldEdge := by
          have hImage (cp : C × P) :
              b.embedding.toFunctionEmbedding '' contractedCarrier U cp ∈ H.oldEdges := by
            rw [hOld]
            have hSrc : contractedCarrier U cp ∈ supportCopies A M := by
              rw [hSupport]
              exact ⟨cp, rfl⟩
            exact supportCopy_image_mem A M S.system.toRelStructure
              b.embedding ⟨contractedCarrier U cp, hSrc⟩
          exact contractedOldEdgeEmbedding U hLinear H
            b.embedding.toFunctionEmbedding hImage

        @[simp] theorem selectedStageActualOldEdgeEmbedding_carrier
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
            (b : DesignatedCopy M D S.system family)
            (H : UniformFillingData S.Vertex X)
            (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
            (cp : C × P) :
            (selectedStageActualOldEdgeEmbedding U A M T hm
              hSupport hLinear D family allowed S b H hOld cp).1 =
              b.embedding.toFunctionEmbedding '' contractedCarrier U cp := rfl

/-- The selected H old edge, after the harmless carrier-subtype
identification, IS the stage's checked selected physical edge of
the corresponding real M support edge. -/
theorem selectedStageOldEdge_eq_selectedPhysical
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
    (b : DesignatedCopy M D S.system family)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (cp : C × P) :
    oldSupportEdgeEmbedding A S.system.toRelStructure H hOld
      (selectedStageActualOldEdgeEmbedding U A M T hm
        hSupport hLinear D family allowed S b H hOld cp) =
      S.selectedPhysicalEdgeEmbedding b
        (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp) := by
          apply Subtype.ext
          change
            (selectedStageActualOldEdgeEmbedding U A M T hm
              hSupport hLinear D family allowed S b H hOld cp).1 =
            b.embedding.toFunctionEmbedding ''
              (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp).1
          rw [selectedStageActualOldEdgeEmbedding_carrier
            U A M T hm hSupport hLinear D family allowed S b H hOld cp,
            contractedPhysicalEdgeEquiv_carrier U A M hSupport hLinear cp]

/-- This genuine selected stage defines the old train on the
complete unchanged physical H old edge type. It is a literal
reindexing of the selected ambient relational train, so no
surjectivity of H's ambient edge-to-wagon map is assumed. -/
noncomputable def selectedStageActualOldTrain
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
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    EdgeTrainLevels H.OldEdge t.length :=
  S.train.restrict
    (oldSupportEdgeEmbedding A S.system.toRelStructure H hOld)

/-- The shorter-train selected-copy relation-preservation/reflection
is now instantiated on the actual old H-edge type of the filling.
The input is the checked source train and genuine selected stage;
the faithful old-H train relation is derived, not supplied. -/
theorem selectedStageActualOldTrain_rel_iff
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
    (μ : Fin (t.length + 1)) (e f : C × P) :
    (contractedChoiceTrain U T hm).rel μ e f ↔
      (selectedStageActualOldTrain U A M T hm hSupport hLinear
        D family allowed S H hOld).rel μ
        (selectedStageActualOldEdgeEmbedding U A M T hm
          hSupport hLinear D family allowed S b H hOld e)
        (selectedStageActualOldEdgeEmbedding U A M T hm
          hSupport hLinear D family allowed S b H hOld f) := by
          change (contractedChoiceTrain U T hm).rel μ e f ↔
            S.train.rel μ
              (oldSupportEdgeEmbedding A S.system.toRelStructure H hOld
                (selectedStageActualOldEdgeEmbedding U A M T hm
                  hSupport hLinear D family allowed S b H hOld e))
              (oldSupportEdgeEmbedding A S.system.toRelStructure H hOld
                (selectedStageActualOldEdgeEmbedding U A M T hm
                  hSupport hLinear D family allowed S b H hOld f))
          rw [selectedStageOldEdge_eq_selectedPhysical
            U A M T hm hSupport hLinear D family allowed S b H hOld e,
            selectedStageOldEdge_eq_selectedPhysical
              U A M T hm hSupport hLinear D family allowed S b H hOld f]
          exact (selectedActualMPhysicalEdgeEmbedding_train_iff
            U A M T hm hSupport hLinear D family allowed S b hb μ e f).symm

end StructuralRamsey.Girth.IndexedPrivateChoice
