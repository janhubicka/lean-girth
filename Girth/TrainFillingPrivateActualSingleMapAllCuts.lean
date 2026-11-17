import Girth.TrainFillingPrivateActualOrderParent
import Girth.TrainFillingPrivateChoiceTaggedEdges
import Girth.TrainFillingIndexedSelectedPhysicalMap
import Girth.TrainFillingInheritedTrain

set_option Elab.async false

/-!
# One actual selected T edge map for every restored train level

Earlier Track 5 candidate proofs built faithful parentwise
realizations separately for each nonterminal cut nu. To use
them for the original T as a WHOLE train one must show that
these cutwise edge maps do not change with nu.

There is a simpler, representation-preserving construction:
fix one genuine selected old OrderStage parent j and one EHN
choice c. Define its selected original physical edge in
the COMPLETE H=N[X] directly by the single canonical
selectedIndexedFilledEdgeEmbedding applied to beta_j and
the source tagged original first-wagon edge.

This map does not mention a cut at all. Its injectivity gives
the restored bottom equality level. The old selected OrderStage
train_iff and the exact H cover give preservation AND reflection
of EVERY shifted positive relation T.rel nu, including the
universal top. No cutwise copy, selected target carrier, or
output train-girth bound is postulated.

The application still needs to identify the original edge type
E(T) with its true (first wagon, local A-support edge) labels
and to combine this edge map with the coloured vertex map and
predicates. Those are not erased by this theorem.

Draft Lean source; exact-head kernel build and axioms audit pending.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (F : C → SummandPrivateTemplate V P X)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (F c).toPrivateWagonInput

/-- The ONE physical selected original edge map into the complete
ambient H, indexed by the actual selected OrderStage parent i and
EHN-selected choice c. It does not depend on any train cut. -/
noncomputable def actualOriginalEdgeInH [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex (U F)))
    {t : List ℕ} (T : EdgeTrainLevels P t.length)
    (hm : 0 < t.length)
    (hSupport : supportCopies A M =
      Set.range (contractedCarrier (U F)))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      (((U F) c).oldCarrier p ∩
        ((U F) c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain (U F) A M T hm
        hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C,
      ((U F) c).templateEdges = H.templateEdges)
    (i : ActualOrderParent (U F) A M T hm
      hSupport hLinear D family allowed S)
    (c : C)
    (e : (F c).OriginalEdge) :
    H.toTrainFilling.NewEdge :=
  selectedIndexedFilledEdgeEmbedding (U F) H hTemplate
    (actualOrderParentOldEdge (U F) A M T hm hSupport
      hLinear D family allowed S H hOld i)
    (selectedTaggedOriginalEdge F c e)

/-- All genuine original edges stay distinct at the fixed
selected (parent,choice) map: no independent output
physical edge injection is taken as a premise. -/
theorem actualOriginalEdgeInH_injective [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex (U F)))
    {t : List ℕ} (T : EdgeTrainLevels P t.length)
    (hm : 0 < t.length)
    (hSupport : supportCopies A M =
      Set.range (contractedCarrier (U F)))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      (((U F) c).oldCarrier p ∩
        ((U F) c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain (U F) A M T hm
        hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C,
      ((U F) c).templateEdges = H.templateEdges)
    (i : ActualOrderParent (U F) A M T hm
      hSupport hLinear D family allowed S)
    (c : C) :
    Function.Injective (actualOriginalEdgeInH F A M T hm
      hSupport hLinear D family allowed S H hOld hTemplate i c) := by
  intro e f hef
  have hTag :
      selectedTaggedOriginalEdge F c e =
        selectedTaggedOriginalEdge F c f :=
    (selectedIndexedFilledEdgeEmbedding (U F) H hTemplate
      (actualOrderParentOldEdge (U F) A M T hm
        hSupport hLinear D family allowed S H hOld i)).injective hef
  exact selectedTaggedOriginalEdge_injective F c hTag

/-- The actual source T-edge bottom equality is preserved AND
reflected by ONE selected map, by its genuine injectivity.
This is not part of a separate cutwise wagon map. -/
theorem actualOriginalEdgeInH_bottom_iff [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex (U F)))
    {t : List ℕ} (T : EdgeTrainLevels P t.length)
    (hm : 0 < t.length)
    (hSupport : supportCopies A M =
      Set.range (contractedCarrier (U F)))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      (((U F) c).oldCarrier p ∩
        ((U F) c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain (U F) A M T hm
        hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C,
      ((U F) c).templateEdges = H.templateEdges)
    (i : ActualOrderParent (U F) A M T hm
      hSupport hLinear D family allowed S)
    (c : C) (e f : (F c).OriginalEdge) :
    ((H.toTrainFilling).inheritedTrain
      (actualSelectedFilledOldTrain (U F) A M T hm
        hSupport hLinear D family allowed
        S.toForestTailStage H hOld)).rel 0
      (actualOriginalEdgeInH F A M T hm hSupport hLinear
        D family allowed S H hOld hTemplate i c e)
      (actualOriginalEdgeInH F A M T hm hSupport hLinear
        D family allowed S H hOld hTemplate i c f)
      ↔ e = f := by
  rw [H.toTrainFilling.inheritedTrain_rel_zero]
  constructor
  · intro hef
    exact actualOriginalEdgeInH_injective F A M T hm
      hSupport hLinear D family allowed S H hOld
      hTemplate i c hef
  · rintro rfl
    rfl

/-- At EVERY old level nu (including its universal top),
the actual selected H-train relation at the RESTORED
level nu.succ is exactly the original source first-wagon
relation. The SAME physical selected original edge map
is used simultaneously for ALL nu. -/
theorem actualOriginalEdgeInH_allPositiveCuts_iff [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex (U F)))
    {t : List ℕ} (T : EdgeTrainLevels P t.length)
    (hm : 0 < t.length)
    (hSupport : supportCopies A M =
      Set.range (contractedCarrier (U F)))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      (((U F) c).oldCarrier p ∩
        ((U F) c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain (U F) A M T hm
        hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplate : ∀ c : C,
      ((U F) c).templateEdges = H.templateEdges)
    (i : ActualOrderParent (U F) A M T hm
      hSupport hLinear D family allowed S)
    (c : C) (ν : Fin (t.length + 1))
    (e f : (F c).OriginalEdge) :
    T.rel ν e.1 f.1 ↔
      ((H.toTrainFilling).inheritedTrain
        (actualSelectedFilledOldTrain (U F) A M T hm
          hSupport hLinear D family allowed
          S.toForestTailStage H hOld)).rel ν.succ
        (actualOriginalEdgeInH F A M T hm hSupport hLinear
          D family allowed S H hOld hTemplate i c e)
        (actualOriginalEdgeInH F A M T hm hSupport hLinear
          D family allowed S H hOld hTemplate i c f) := by
  let β := actualOrderParentOldEdge (U F) A M T hm
    hSupport hLinear D family allowed S H hOld i
  let oldTrain := actualSelectedFilledOldTrain (U F) A M T hm
    hSupport hLinear D family allowed S.toForestTailStage H hOld
  have hComponent :
      T.rel ν e.1 f.1 ↔
        (contractedChoiceTrain (U F) T hm).rel ν
          (c, e.1) (c, f.1) := by
    change T.rel ν e.1 f.1 ↔
      ν.val = t.length ∨ (c = c ∧ T.rel ν e.1 f.1)
    constructor
    · intro h
      exact Or.inr ⟨rfl, h⟩
    · rintro (hTop | ⟨_, hRel⟩)
      · have hν :
          ν = (⟨t.length, Nat.lt_succ_self t.length⟩ :
            Fin (t.length + 1)) := Fin.ext hTop
        rw [hν]
        exact T.top e.1 f.1
      · exact hRel
  have hFaithful :
      (contractedChoiceTrain (U F) T hm).rel ν
          (c, e.1) (c, f.1) ↔
        oldTrain.rel ν (β (c, e.1)) (β (c, f.1)) :=
    actualOrderParentOldEdge_faithful (U F) A M T hm
      hSupport hLinear D family allowed S H hOld
      i ν (c, e.1) (c, f.1)
  calc
    T.rel ν e.1 f.1 ↔
        (contractedChoiceTrain (U F) T hm).rel ν
          (c, e.1) (c, f.1) := hComponent
    _ ↔ oldTrain.rel ν (β (c, e.1)) (β (c, f.1)) := hFaithful
    _ ↔ ((H.toTrainFilling).inheritedTrain oldTrain).rel ν.succ
          (actualOriginalEdgeInH F A M T hm
            hSupport hLinear D family allowed S H hOld
            hTemplate i c e)
          (actualOriginalEdgeInH F A M T hm
            hSupport hLinear D family allowed S H hOld
            hTemplate i c f) := by
        rw [H.toTrainFilling.inheritedTrain_rel_succ]
        simp only [actualOriginalEdgeInH,
          selectedIndexedFilledEdgeEmbedding_cover,
          selectedTaggedOriginalEdge]
        rfl

end StructuralRamsey.Girth.IndexedPrivateChoice
