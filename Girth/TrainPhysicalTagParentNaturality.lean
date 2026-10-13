import Girth.TrainPhysicalPictureGeneratedTrain
import Girth.TrainSharedEdgeQuotients

/-!
# Generated shared/private wagon tags commute with parent quotients

At each cut the generated physical picture has a shared/private
wagon tag. The canonical old/core quotient-parent maps commute
with these tags even when a private child acquires a shared parent.

This is a direct one-edge normal-form calculation and uses exact
preservation/reflection of the old/core train embedding on the
genuine gluing support edges at every cut. It does NOT assert
parent-parameter inequalities or the existence of a Ramsey witness.

The separate quotient-of-the-GENERATED-train to tagged-node
equivalence is still needed to turn this pointwise equality into
a full parent-map equivalence on all generated wagon classes.
-/

namespace StructuralRamsey.Girth

universe v
variable {Shared OldEdge CoreEdge I : Type v}

/-- At a cut μ, genuine shared-old and core edge quotient labels
determine the optional contact of their parent wagon classes.
No old quotient class is identified merely by its vertex carrier. -/
noncomputable def physicalPictureCutGlue
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge) :
    I → Quotient (Told.wagonSetoid μ) →
      Option (Quotient (Tcore.wagonSetoid μ)) :=
  wagonContactGlue
    (wagonSharedEdgeContact
      (oldSharedWagonLabel Told μ (fun _ : I => inOld))
      (oldSharedWagonLabel Tcore μ inCore))

/-- The exact shared/private wagon ancestor tag of one physical
core-or-private edge at a selected horizontal cut. -/
noncomputable def physicalPictureCutTag
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge) :
    PhysicalPictureEdge inOld I CoreEdge →
      (Quotient (Tcore.wagonSetoid μ)) ⊕
        (I × Quotient (Told.wagonSetoid μ)) :=
  physicalPictureWagonTag inOld
    (fun b : CoreEdge => Quotient.mk (Tcore.wagonSetoid μ) b)
    (fun a : OldEdge => Quotient.mk (Told.wagonSetoid μ) a)
    (physicalPictureCutGlue Told Tcore μ inOld inCore)

/-- Exact parent compatibility of physical shared/private ancestor
labels at ANY two nested cuts, including private-to-shared parent
transitions. The statement concerns genuine source EDGE labels,
not the equality of their potentially duplicated vertex carriers. -/
theorem physicalPictureCutTag_parent
    {m : ℕ}
    (Told : EdgeTrainLevels OldEdge m)
    (Tcore : EdgeTrainLevels CoreEdge m)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (inOld : Shared ↪ OldEdge)
    (inCore : I → Shared ↪ CoreEdge)
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
      Told.rel κ (inOld s) (inOld t) ↔
        Tcore.rel κ (inCore i s) (inCore i t))
    (e : PhysicalPictureEdge inOld I CoreEdge) :
    physicalPictureCutTag Told Tcore ν inOld inCore e =
      gluedWagonParent
        (physicalPictureCutGlue Told Tcore μ inOld inCore)
        (physicalPictureCutGlue Told Tcore ν inOld inCore)
        (Tcore.wagonParent μ ν hμν)
        (Told.wagonParent μ ν hμν)
        (physicalPictureCutTag Told Tcore μ inOld inCore e) := by
  have hCompat : ∀ i u c,
      physicalPictureCutGlue Told Tcore μ inOld inCore i u = some c →
      physicalPictureCutGlue Told Tcore ν inOld inCore
        i (Told.wagonParent μ ν hμν u) =
        some (Tcore.wagonParent μ ν hμν c) := by
    intro i u c h
    exact sharedWagonQuotient_contact_parent
      Told Tcore μ ν hμν
      (fun _ : I => inOld) inCore
      (by
        intro κ j s t
        exact hRel κ j s t)
      i u c h
  cases e with
  | inl b =>
    change
      (Sum.inl (Quotient.mk (Tcore.wagonSetoid ν) b) :
        Quotient (Tcore.wagonSetoid ν) ⊕
          (I × Quotient (Told.wagonSetoid ν))) =
        Sum.inl (Tcore.wagonParent μ ν hμν
          (Quotient.mk (Tcore.wagonSetoid μ) b))
    rfl
  | inr z =>
    rcases z with ⟨i, a⟩
    have hStd :=
      gluedWagonParent_standard
        (physicalPictureCutGlue Told Tcore μ inOld inCore)
        (physicalPictureCutGlue Told Tcore ν inOld inCore)
        (Tcore.wagonParent μ ν hμν)
        (Told.wagonParent μ ν hμν)
        hCompat i (Quotient.mk (Told.wagonSetoid μ) a.1)
    change
      gluedStandardNode
        (physicalPictureCutGlue Told Tcore ν inOld inCore)
        i (Quotient.mk (Told.wagonSetoid ν) a.1) =
      gluedWagonParent
        (physicalPictureCutGlue Told Tcore μ inOld inCore)
        (physicalPictureCutGlue Told Tcore ν inOld inCore)
        (Tcore.wagonParent μ ν hμν)
        (Told.wagonParent μ ν hμν)
        (gluedStandardNode
          (physicalPictureCutGlue Told Tcore μ inOld inCore)
          i (Quotient.mk (Told.wagonSetoid μ) a.1))
    simpa only [EdgeTrainLevels.wagonParent_mk] using hStd.symm

end StructuralRamsey.Girth
