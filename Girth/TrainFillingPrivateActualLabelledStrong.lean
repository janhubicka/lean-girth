import Girth.TrainFillingPrivateActualOrderStrictMono
import Girth.TrainFillingPrivateCanonicalTargetStrong

set_option Elab.async false

/-!
# Genuine selected OrderStage -> labelled strongly induced H target

The shorter RR_h OrderStage contains the selected relational
M-copies j, their actual A-strongness in N and their faithful
train-cut restrictions. Each selected j has a physical old-edge
embedding beta_j whose image is EXACTLY all full A-support
edges inside j(M).

The actual order-derived parentwise realization constructs:
  * the vertex map j, all full filled physical edge maps;
  * all exact target copy-edge ranges;
  * all proper-wagon quotient embeddings;
  * sibling-disjoint choice components indexed by (j,c).
The generic checked component-scattering lemma then makes each
target STRONGLY induced in full H=N[X] from genuine OLD
OrderStage strongness. No output target strongness, output girth,
or ambient edge deletion is assumed.

This is an endpoint for the strong-target part of the cutoff-two
application. The remaining unproved application is the
genuine covered/order-selected EHN witness; the original T
edge/colour/order/train map is handled by separate Track 5
candidate modules. The actual H-system girth is transferred
at every proper cut using OrderStage.allCutGirth.

Uncompiled Lean source; do not assign validation marks.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- A genuine selected OrderStage supplies the old-parent
strongness required by the canonical full-filled scattering
record. It is an actual theorem of S.strong and beta_j's
complete old support range, not a new output hypothesis. -/
theorem actualOrderStage_oldParentStrong [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    let vertex := actualOrderParentVertex U A M T hm
      hSupport hLinear D family allowed S
    let β := actualOrderParentOldEdge U A M T hm
      hSupport hLinear D family allowed S H hOld
    ∀ i : ActualOrderParent U A M T hm
        hSupport hLinear D family allowed S,
      ∀ f : H.OldEdge,
        ¬ (f.1 ∩ Set.range (vertex i)).Subsingleton →
          f ∈ Set.range (β i) := by
  intro i f hMeet
  exact actualOrderParent_oldStrong U A M T hm
    hSupport hLinear D family allowed S H hOld i f hMeet

/-- The ACTUAL target in H selected by the pair (j,c) is
strongly induced. The only order assumptions are those needed
to derive the genuine filled G0-to-H carrier map; its
strongness then follows from the checked scattering theorem
using the REAL old OrderStage selected M-copy j.

Distinct selected old parents may overlap. The universal top
is not treated as a separate tagged wagon and no bound at
that top is required. -/
theorem actualOrderStage_labelledTargetStrong_of_strictMono
    [Nontrivial X] [Finite X] [LinearOrder X] [LinearOrder (Vertex U)]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    [PartialOrder S.Vertex]
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)))
    (hSelectedMono : ∀ i : ActualOrderParent U A M T hm
        hSupport hLinear D family allowed S,
      StrictMono (fun z : Vertex U =>
        (actualOrderParentVertex U A M T hm
          hSupport hLinear D family allowed S i) z))
    (hCanonicalMono : ∀ f : H.OldEdge, StrictMono (H.place f))
    (ν : Fin (t.length + 1)) (hProper : ν.val < t.length)
    (j : ActualOrderParent U A M T hm
      hSupport hLinear D family allowed S × C) :
    let R := actualOrderStageFaithfulParentwise_of_strictMono
      U A M T hm hSupport hLinear D family allowed S
        H hOld hTemplate hLocal hSourceMono hSelectedMono
          hCanonicalMono ν hProper
    ∀ (e : H.toTrainFilling.NewEdge) (x y : S.Vertex),
      x ≠ y → x ∈ e.1 → y ∈ e.1 →
      x ∈ R.toParentwiseRealization.targetCarrier j →
      y ∈ R.toParentwiseRealization.targetCarrier j →
      e ∈ R.toParentwiseRealization.targetEdges j := by
  let vertex := actualOrderParentVertex U A M T hm
    hSupport hLinear D family allowed S
  let β := actualOrderParentOldEdge U A M T hm
    hSupport hLinear D family allowed S H hOld
  let oldTrain := actualSelectedFilledOldTrain U A M T hm
    hSupport hLinear D family allowed S.toForestTailStage H hOld
  have hFaithful : ∀ i : ActualOrderParent U A M T hm
        hSupport hLinear D family allowed S,
      ∀ a b : C × P,
        (contractedChoiceTrain U T hm).rel ν a b ↔
        oldTrain.rel ν (β i a) (β i b) := by
    intro i a b
    exact actualOrderParentOldEdge_faithful U A M T hm
      hSupport hLinear D family allowed S H hOld i ν a b
  have hEdgeCarrier :
      ∀ i : ActualOrderParent U A M T hm
          hSupport hLinear D family allowed S,
        ∀ a : Edge U,
          (selectedIndexedFilledEdgeEmbedding U H hTemplate
            (β i) a).1 =
            vertex i '' edgeCarrier U a := by
    intro i a
    exact actualOrderParent_filledEdgeCarrier_of_strictMono U A M
      T hm hSupport hLinear D family allowed S H hOld
      hTemplate hSourceMono hSelectedMono hCanonicalMono i a
  have hOldStrong :
      ∀ i : ActualOrderParent U A M T hm
          hSupport hLinear D family allowed S,
        ∀ f : H.OldEdge,
          ¬ (f.1 ∩ Set.range (vertex i)).Subsingleton →
            f ∈ Set.range (β i) :=
    actualOrderStage_oldParentStrong U A M T hm hSupport
      hLinear D family allowed S H hOld
  exact canonicalFilledSelected_targetStrong U H hTemplate
    vertex β T hm oldTrain ν hProper hLocal hFaithful
    hEdgeCarrier hOldStrong j

end StructuralRamsey.Girth.IndexedPrivateChoice
