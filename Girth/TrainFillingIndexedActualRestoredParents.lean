import Girth.TrainFillingIndexedContractedTrain
import Girth.TrainFillingIndexedSelectedPhysicalMap
import Girth.TrainFillingIndexedProperWagonReconstruction

set_option Elab.async false

/-!
# Genuine contracted-to-restored proper wagon reflection

A genuinely selected shorter-train M-copy preserves AND reflects the
train relation on its complete first-wagon edges at each proper cut.
The already checked indexed physical G0→H edge embedding covers the
actual selected M edge, and the restored train pulls its positive
level relation back through that cover.

Therefore equality of the true tagged source quotient wagon names is
equivalent to equality of the ACTUAL restored H quotient wagons.
Construct the wagon injection from this equivalence; do not assume an
independent ambient wagon map or rename quotient labels by carriers.

This is a conditional proper-cut application bridge. The real
selected train-faithfulness is an explicit condition to be obtained
from the shorter-train Ramsey witness, not a new output assumption.
No universal-top tagged quotient is claimed; at the top all choice
components legitimately share one wagon. No appendix is involved.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Y : Type v}
variable (U : C → PrivateWagonInput V P X)
variable (H : UniformFillingData Y X)
variable (hTemplate : ∀ c : C, (U c).templateEdges = H.templateEdges)

/-- Faithful physical selected old-edge cut relations imply exact
parent equality reflection for EVERY filled G0 physical edge.
The parent on the right is the real restored quotient of H edges
at the positive cut nu.succ. -/
theorem selectedIndexedRestoredParent_iff
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (β : (C × P) ↪ H.OldEdge)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hFaithful : ∀ e f : C × P,
      (contractedChoiceTrain U T hm).rel ν e f ↔
        S.rel ν (β e) (β f))
    (a b : Edge U) :
    properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) a =
        properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) b ↔
      (Quotient.mk
          (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ)
          (selectedIndexedFilledEdgeEmbedding U H hTemplate β a)) =
      (Quotient.mk
          (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ)
          (selectedIndexedFilledEdgeEmbedding U H hTemplate β b)) := by
          have hOld :
              properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) a =
                properParentOf U (fun p => Quotient.mk (T.wagonSetoid ν) p) b ↔
              (contractedChoiceTrain U T hm).rel ν
                (a.1, a.2.1) (b.1, b.2.1) := by
            change contractedProperParent U T ν (a.1, a.2.1) =
                contractedProperParent U T ν (b.1, b.2.1) ↔ _
            exact contractedProperParent_eq_iff_rel U T hm ν hProper
              (a.1, a.2.1) (b.1, b.2.1)
          constructor
          · intro hp
            have hr : S.rel ν (β (a.1, a.2.1)) (β (b.1, b.2.1)) :=
              (hFaithful (a.1, a.2.1) (b.1, b.2.1)).mp (hOld.mp hp)
            apply Quotient.sound
            apply (H.toTrainFilling.inheritedTrain_rel_succ S ν
              (selectedIndexedFilledEdgeEmbedding U H hTemplate β a)
              (selectedIndexedFilledEdgeEmbedding U H hTemplate β b)).mpr
            simpa only [selectedIndexedFilledEdgeEmbedding_cover] using hr
          · intro hp
            have hr :
                (H.toTrainFilling.inheritedTrain S).rel ν.succ
                  (selectedIndexedFilledEdgeEmbedding U H hTemplate β a)
                  (selectedIndexedFilledEdgeEmbedding U H hTemplate β b) :=
              Quotient.exact hp
            have hs : S.rel ν (β (a.1, a.2.1)) (β (b.1, b.2.1)) := by
              have hh := (H.toTrainFilling.inheritedTrain_rel_succ S ν
                (selectedIndexedFilledEdgeEmbedding U H hTemplate β a)
                (selectedIndexedFilledEdgeEmbedding U H hTemplate β b)).mp hr
              simpa only [selectedIndexedFilledEdgeEmbedding_cover] using hh
            exact hOld.mpr
              ((hFaithful (a.1, a.2.1) (b.1, b.2.1)).mpr hs)

/-- The actual restored quotient wagon injection is CONSTRUCTED from
the selected physical edge embedding and faithful shorter-train
relations. Only source wagon representability is needed; there is no
ambient quotient surjectivity requirement. -/
noncomputable def selectedIndexedRestoredWagonEmbedding
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (β : (C × P) ↪ H.OldEdge)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ e f : C × P,
      (contractedChoiceTrain U T hm).rel ν e f ↔
        S.rel ν (β e) (β f)) :
    ProperWagon (Q := Quotient (T.wagonSetoid ν)) U ↪
      Quotient (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ) := by
          have hParent : Function.Surjective
              (fun p : P => Quotient.mk (T.wagonSetoid ν) p) := by
            intro q
            induction q using Quotient.inductionOn with
            | h p => exact ⟨p, rfl⟩
          exact reconstructedProperWagonEmbedding U
            (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
            (selectedIndexedFilledEdgeEmbedding U H hTemplate β)
            (fun e : H.toTrainFilling.NewEdge =>
              Quotient.mk (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ) e)
            hParent hLocal
            (selectedIndexedRestoredParent_iff U H hTemplate
              T hm S β ν hProper hFaithful)

/-- The constructed wagon map commutes with physical parents on all
actual heterogeneous G0 edges. No independently assumed wagon image
equality is used. -/
theorem selectedIndexedRestoredWagonEmbedding_parent
    {m : ℕ} (T : EdgeTrainLevels P m) (hm : 0 < m)
    (S : EdgeTrainLevels H.OldEdge m)
    (β : (C × P) ↪ H.OldEdge)
    (ν : Fin (m + 1)) (hProper : ν.val < m)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hFaithful : ∀ e f : C × P,
      (contractedChoiceTrain U T hm).rel ν e f ↔
        S.rel ν (β e) (β f))
    (a : Edge U) :
    selectedIndexedRestoredWagonEmbedding U H hTemplate
      T hm S β ν hProper hLocal hFaithful
      (properParentOf U
        (fun p => Quotient.mk (T.wagonSetoid ν) p) a) =
      Quotient.mk
        (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ)
        (selectedIndexedFilledEdgeEmbedding U H hTemplate β a) := by
          have hParent : Function.Surjective
              (fun p : P => Quotient.mk (T.wagonSetoid ν) p) := by
            intro q
            induction q using Quotient.inductionOn with
            | h p => exact ⟨p, rfl⟩
          exact reconstructedProperWagonEmbedding_parent U
            (fun p : P => Quotient.mk (T.wagonSetoid ν) p)
            (selectedIndexedFilledEdgeEmbedding U H hTemplate β)
            (fun e : H.toTrainFilling.NewEdge =>
              Quotient.mk (((H.toTrainFilling).inheritedTrain S).wagonSetoid ν.succ) e)
            hParent hLocal
            (selectedIndexedRestoredParent_iff U H hTemplate
              T hm S β ν hProper hFaithful) a

end StructuralRamsey.Girth.IndexedPrivateChoice
