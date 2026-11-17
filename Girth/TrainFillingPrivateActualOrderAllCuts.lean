import Girth.TrainFillingPrivateCanonicalAllCuts
import Girth.TrainFillingPrivateActualOrderRealization

set_option Elab.async false

/-!
# Actual shorter OrderStage supplies the entire all-cut train reflection

One genuine selected shorter OrderStage fixes both the physical
old-edge injection beta and the vertex map. Its checked/constructed
train faithfulness is uniform over every old cut.

We specialize the canonical simultaneous-cut lemma to these actual
data. The ONLY extra geometric input at this level is the exact
full physical carrier identity. It can be obtained separately by
the ordered-coordinate lemma. No chosen cutwise realizations, no
hImage coherence equation, and no independently postulated old-train
faithfulness are inputs here.

This remains an uncompiled source candidate.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (K : C → SummandPrivateTemplate V P X)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (K c).toPrivateWagonInput

/-- The SAME selected old OrderStage parent maps the original target
physical edges faithfully at all proper inherited cuts. -/
theorem actualOrderStageOriginalEdge_allProperCuts_iff [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex (U K)))
    {t : List ℕ} (T : EdgeTrainLevels P t.length)
    (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier (U K)))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      (((U K) c).oldCarrier p ∩ ((U K) c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain (U K) A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, ((U K) c).templateEdges = H.templateEdges)
    (hLocal : ∀ c : C, Nonempty ((U K) c).LocalEdge)
    (hEdgeCarrier :
      ∀ (i : ActualOrderParent (U K) A M T hm hSupport
          hLinear D family allowed S) (a : Edge (U K)),
        (selectedIndexedFilledEdgeEmbedding (U K) H hTemplate
          (actualOrderParentOldEdge (U K) A M T hm hSupport
            hLinear D family allowed S H hOld i) a).1 =
        (actualOrderParentVertex (U K) A M T hm hSupport
          hLinear D family allowed S i) '' edgeCarrier (U K) a)
    (i : ActualOrderParent (U K) A M T hm
      hSupport hLinear D family allowed S)
    (c : C) :
    ∀ (ν : Fin (t.length + 1)), ν.val < t.length →
      ∀ e f : (K c).OriginalEdge,
        T.rel ν e.1 f.1 ↔
          Quotient.mk
            (((H.toTrainFilling).inheritedTrain
              (actualSelectedFilledOldTrain (U K) A M T hm
                hSupport hLinear D family allowed
                S.toForestTailStage H hOld)).wagonSetoid ν.succ)
            (selectedIndexedFilledEdgeEmbedding (U K) H hTemplate
              (actualOrderParentOldEdge (U K) A M T hm hSupport
                hLinear D family allowed S H hOld i)
              (selectedTaggedOriginalEdge K c e)) =
          Quotient.mk
            (((H.toTrainFilling).inheritedTrain
              (actualSelectedFilledOldTrain (U K) A M T hm
                hSupport hLinear D family allowed
                S.toForestTailStage H hOld)).wagonSetoid ν.succ)
            (selectedIndexedFilledEdgeEmbedding (U K) H hTemplate
              (actualOrderParentOldEdge (U K) A M T hm hSupport
                hLinear D family allowed S H hOld i)
              (selectedTaggedOriginalEdge K c f)) := by
  exact canonicalOriginalEdge_allProperCuts_iff K H hTemplate
    (actualOrderParentVertex (U K) A M T hm hSupport
      hLinear D family allowed S)
    (actualOrderParentOldEdge (U K) A M T hm hSupport
      hLinear D family allowed S H hOld)
    T hm
    (actualSelectedFilledOldTrain (U K) A M T hm
      hSupport hLinear D family allowed S.toForestTailStage H hOld)
    hLocal
    (fun ν _ j a b =>
      actualOrderParentOldEdge_faithful (U K)
        A M T hm hSupport hLinear D family allowed
        S H hOld j ν a b)
    hEdgeCarrier i c

end StructuralRamsey.Girth.IndexedPrivateChoice
