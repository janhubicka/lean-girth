import Girth.TrainFillingPrivateCanonicalParentwise
import Girth.TrainFillingPrivateOriginalTrainInH

set_option Elab.async false

/-!
# All proper cuts of a single canonical filled target

The physical edge injection into H=N[X] is the SAME
  selectedIndexedFilledEdgeEmbedding U H hTemplate (β i)
at every cut. Only the canonical quotient parent of H changes with ν.
Consequently no independent cut-coherence equality of edge maps is
needed when the realizations come from this canonical constructor.

The source-train faithfulness and exact full carrier conditions
remain explicit, and must be obtained from one actual OrderStage.
This file does not manufacture the shorter Ramsey witness or output girth.

Source-level candidate: exact-head Lean elaboration still required.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y I : Type v}
variable (S : C → SummandPrivateTemplate V P X)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (S c).toPrivateWagonInput

/-- One canonical filled ambient H and one fixed physical original
edge embedding preserve/reflect all proper restored cuts. The old
selected edge injection β does not depend on ν. The inherited quotient
at ν.succ is the ONLY varying ambient object.

This replaces the abstract hImage compatibility input of
selectedOriginalEdge_allProperCuts_iff at the canonical filling level.
-/
theorem canonicalOriginalEdge_allProperCuts_iff
    (H : UniformFillingData Y X)
    (hTemplate : ∀ c : C, (U S c).templateEdges = H.templateEdges)
    (vertex : I → Vertex (U S) ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (oldTrain : EdgeTrainLevels H.OldEdge m)
    (hLocal : ∀ c : C, Nonempty (U S c).LocalEdge)
    (hFaithful : ∀ (ν : Fin (m + 1)), ν.val < m →
      ∀ (i : I) (a b : C × P),
        (contractedChoiceTrain (U S) T hm).rel ν a b ↔
          oldTrain.rel ν (β i a) (β i b))
    (hEdgeCarrier : ∀ (i : I) (a : Edge (U S)),
      (selectedIndexedFilledEdgeEmbedding (U S) H hTemplate
        (β i) a).1 = vertex i '' edgeCarrier (U S) a)
    (i : I) (c : C) :
    ∀ (ν : Fin (m + 1)), ν.val < m →
      ∀ e f : (S c).OriginalEdge,
        T.rel ν e.1 f.1 ↔
          Quotient.mk
              (((H.toTrainFilling).inheritedTrain oldTrain).wagonSetoid ν.succ)
              (selectedIndexedFilledEdgeEmbedding (U S) H
                hTemplate (β i) (selectedTaggedOriginalEdge S c e)) =
          Quotient.mk
              (((H.toTrainFilling).inheritedTrain oldTrain).wagonSetoid ν.succ)
              (selectedIndexedFilledEdgeEmbedding (U S) H
                hTemplate (β i) (selectedTaggedOriginalEdge S c f)) := by
  intro ν hProper e f
  let R :=
    (canonicalFilledSelectedFaithfulRealization_of_carrier
      (U S) H hTemplate vertex β T hm oldTrain ν hProper
        hLocal (fun j a b => hFaithful ν hProper j a b)
        hEdgeCarrier).toParentwiseRealization
  have hCut :=
    ParentwiseRealization.selectedOriginalEdge_wagon_iff
      S T ν hProper
      (canonicalFilledSelectedData (U S) H vertex β oldTrain ν)
      R i c e f
  -- R.edge is the fixed selectedIndexedFilledEdgeEmbedding;
  -- D.parent is the inherited quotient at ν.succ.
  simpa only [R, canonicalFilledSelectedFaithfulRealization_of_carrier,
    FaithfulParentwisePhysicalRealization.toParentwiseRealization,
    canonicalFilledSelectedData] using hCut

/-- The canonical physical edge injection is fixed independently of
every cut and is injective. This is the bottom equality case. -/
theorem canonicalOriginalEdge_injective
    (H : UniformFillingData Y X)
    (hTemplate : ∀ c : C, (U S c).templateEdges = H.templateEdges)
    (β : I → (C × P) ↪ H.OldEdge)
    (i : I) (c : C) :
    Function.Injective (fun e : (S c).OriginalEdge =>
      selectedIndexedFilledEdgeEmbedding (U S) H hTemplate
        (β i) (selectedTaggedOriginalEdge S c e)) := by
  intro e f h
  exact selectedTaggedOriginalEdge_injective S c
    ((selectedIndexedFilledEdgeEmbedding (U S) H hTemplate
      (β i)).injective h)

end StructuralRamsey.Girth.IndexedPrivateChoice
