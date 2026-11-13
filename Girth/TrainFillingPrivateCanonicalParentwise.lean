import Girth.TrainFillingIndexedFaithfulParentwise
import Girth.TrainFillingIndexedActualRestoredParents

set_option Elab.async false

/-!
# Canonical parentwise realization in the FULL filled ambient system

Fix the actual old train of N, one restored proper cut and an
injection beta_i of all contracted first wagons of each selected
old parent i into the actual N old physical edges. A selected
vertex embedding v_i carries the whole heterogeneous G0.

The CANONICAL old-parent records in N[X] are:
  copyCarrier(i) = range(v_i),
  copyEdges(i) = {full filled H edges e | cover(e) is in range(beta_i)}.
They keep all ambient H edges and all quotient wagon labels.

This file constructs every field of
FaithfulParentwisePhysicalRealization from:
* actual source train relation reflection of beta_i;
* exact canonical X-point placements on each selected first wagon;
* genuine nonemptiness of the common X-template edge type.

In particular, NO output copyEdges equality, parent injection,
parent-commutation equation, edge-carrier equation or output girth
is postulated. The existing checked indexed range, carrier and
restored-parent lemmas prove them.

The actual cutoff-two call site still needs to instantiate beta_i
and v_i from one selected shorter OrderStage M-copy and establish
pointwise canonical-placement compatibility using the selected
orders. The previous Track 5 candidate modules now construct beta_i
and its all-cut train faithfulness from that actual stage.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v

variable {C V P X Y I : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Complete old-parent designated data for the unchanged filled
system H=N[X]. No ambient edge is discarded: only copyEdges(i)
selects the cover-pullback belonging to each designated parent. -/
noncomputable def canonicalFilledSelectedData
    (H : UniformFillingData Y X)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1)) :
    OrderOneData Y H.toTrainFilling.NewEdge I
      (Quotient (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ)) where
  edgeCarrier := fun e => e.1
  copyCarrier := fun i => Set.range (vertex i)
  copyEdges := fun i =>
    {e | H.toTrainFilling.cover e ∈ Set.range (β i)}
  parent := fun e =>
    Quotient.mk (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ) e

/-- This formulation asks only for exact physical filled-edge
carriers, the precise geometric field of global scattering.
The ordered-carrier theorem can supply it without separately
identifying every X-coordinate pointwise. -/
/-- The exact physical-edge carrier statement suffices for the
faithful parentwise realization. The constructed record has
physical and quotient-wagon injectivity and all exact image laws.
Only *input* train faithfulness and literal canonical placement
compatibility are premises; neither output girth nor output
parentwise identity is assumed. -/
noncomputable def canonicalFilledSelectedFaithfulRealization_of_carrier
    (H : UniformFillingData Y X)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ i : I, ∀ a b : C × P,
      (contractedChoiceTrain U T hm).rel ν a b ↔
        S.rel ν (β i a) (β i b))
    (hEdgeCarrier : ∀ (i : I) (a : Edge U),
      (selectedIndexedFilledEdgeEmbedding U H hTemplate (β i) a).1 =
        vertex i '' edgeCarrier U a) :
    FaithfulParentwisePhysicalRealization U
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
      (canonicalFilledSelectedData U H vertex β S ν) where
  vertex := vertex
  edge := fun i => selectedIndexedFilledEdgeEmbedding U H hTemplate (β i)
  parent_surjective := by
    intro q
    induction q using Quotient.inductionOn with
    | h p => exact ⟨p, rfl⟩
  template_nonempty := hLocal
  edge_parent_faithful := by
    intro i a b
    change
      properParentOf U
        (fun p : P => Quotient.mk (T.wagonSetoid ν) p) a =
          properParentOf U
            (fun p : P => Quotient.mk (T.wagonSetoid ν) p) b ↔
        (Quotient.mk
          (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ)
            (selectedIndexedFilledEdgeEmbedding U H hTemplate (β i) a)) =
        (Quotient.mk
          (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ)
            (selectedIndexedFilledEdgeEmbedding U H hTemplate (β i) b))
    exact selectedIndexedRestoredParent_iff U H hTemplate T hm S
      (β i) ν hProper (hFaithful i) a b
  edgeCarrier_eq := hEdgeCarrier
  copyCarrier_eq := by
    intro i
    rfl
  copyEdges_eq := by
    intro i
    exact (selectedIndexedFilledEdgeEmbedding_range
      U H hTemplate (β i)).symm

/-- The actual selected canonical filling data admit a genuine
faithful parentwise realization. The constructed record has
physical and quotient-wagon injectivity and all exact image laws.
Only *input* train faithfulness and literal canonical placement
compatibility are premises; neither output girth nor output
parentwise identity is assumed. -/
noncomputable def canonicalFilledSelectedFaithfulRealization
    (H : UniformFillingData Y X)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ i : I, ∀ a b : C × P,
      (contractedChoiceTrain U T hm).rel ν a b ↔
        S.rel ν (β i a) (β i b))
    (hPlace : ∀ (i : I) (c : C) (p : P) (x : X),
      H.place (β i (c, p)) x =
        vertex i (tagVertex U c ((U c).place p x))) :
    FaithfulParentwisePhysicalRealization U
      (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
      (canonicalFilledSelectedData U H vertex β S ν) :=
  canonicalFilledSelectedFaithfulRealization_of_carrier
    U H hTemplate vertex β T hm S ν hProper hLocal hFaithful
    (fun i a =>
      selectedIndexedFilledEdgeEmbedding_carrier
        U H hTemplate (β i) (vertex i) (hPlace i) a)

/-- Once the OLD full system-girth bound is supplied by the genuine
shorter OrderStage and the canonical filling theorem, the resulting
selected (parent,choice)-indexed family inherits exactly that
full-system-girth bound by the already checked global scattering.
No new bound is assumed on the output target. -/
theorem canonicalFilledSelected_targetFullSystemGirthGT
    (H : UniformFillingData Y X)
    (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)
    (vertex : I → Vertex U ↪ Y)
    (β : I → (C × P) ↪ H.OldEdge)
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ i : I, ∀ a b : C × P,
      (contractedChoiceTrain U T hm).rel ν a b ↔
        S.rel ν (β i a) (β i b))
    (hPlace : ∀ (i : I) (c : C) (p : P) (x : X),
      H.place (β i (c, p)) x =
        vertex i (tagVertex U c ((U c).place p x)))
    {g : ℕ}
    (hOldFilled :
      (canonicalFilledSelectedData U H vertex β S ν).FullSystemGirthGT g) :
    (((canonicalFilledSelectedFaithfulRealization U H hTemplate
        vertex β T hm S ν hProper hLocal hFaithful hPlace)
        .toParentwiseRealization).designatedFamily.target).FullSystemGirthGT g := by
  exact (canonicalFilledSelectedFaithfulRealization U H hTemplate
    vertex β T hm S ν hProper hLocal hFaithful hPlace).target_fullSystemGirthGT hOldFilled

end StructuralRamsey.Girth.IndexedPrivateChoice
