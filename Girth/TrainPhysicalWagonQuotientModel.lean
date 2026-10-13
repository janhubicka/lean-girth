import Girth.TrainPhysicalGeneratedTagCarrier
import Girth.TrainSharedEdgeQuotients
import Girth.TrainParameterRestriction

/-!
# Actual generated wagon quotients and their shared/private model

The edge normal form gives an injective map from actual quotient wagons
into shared/private source labels. This map commutes with every nested
parent map and identifies complete vertex carriers. Hence a parent
intersection bound proved for source labels transfers to the generated
physical train. Neither carrier injectivity nor a witness bridge is
assumed by the representation lemmas.

The final parameter transfer is explicitly conditional on the source-label
bound; it does not prove the interior order-one bridge or system girth.
-/

namespace StructuralRamsey.Girth.PhysicalWagonModel

universe v
variable {I Shared OldEdge CoreEdge W : Type v} {m : ℕ}
variable (Told : EdgeTrainLevels OldEdge m)
variable (Tcore : EdgeTrainLevels CoreEdge m)
variable (inOld : Shared ↪ OldEdge)
variable (inCore : I → Shared ↪ CoreEdge)

/-- Contact is witnessed by an actual shared edge. -/
noncomputable def contact (μ : Fin (m + 1)) :
    I → Quotient (Told.wagonSetoid μ) →
      Option (Quotient (Tcore.wagonSetoid μ)) :=
  wagonContactGlue (wagonSharedEdgeContact
    (oldSharedWagonLabel Told μ (fun _ : I => inOld))
    (oldSharedWagonLabel Tcore μ inCore))

/-- Canonical shared/private label of a physical edge at a cut. -/
noncomputable def edgeTag (μ : Fin (m + 1)) :
    PhysicalPictureEdge inOld I CoreEdge →
      Quotient (Tcore.wagonSetoid μ) ⊕
        (I × Quotient (Told.wagonSetoid μ)) :=
  physicalPictureWagonTag inOld
    (Quotient.mk (Tcore.wagonSetoid μ))
    (Quotient.mk (Told.wagonSetoid μ))
    (contact Told Tcore inOld inCore μ)

variable (hShared : ∀ i : I, Nonempty Shared)
variable (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
  Told.rel κ (inOld s) (inOld t) ↔
    Tcore.rel κ (inCore i s) (inCore i t))

/-- The established edge normal form, expressed with genuine quotient labels. -/
theorem rel_iff_edgeTag
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
  Told.rel κ (inOld s) (inOld t) ↔
    Tcore.rel κ (inCore i s) (inCore i t)) (μ : Fin (m + 1))
    (a b : PhysicalPictureEdge inOld I CoreEdge) :
    (physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).rel μ a b ↔
      edgeTag Told Tcore inOld inCore μ a =
        edgeTag Told Tcore inOld inCore μ b := by
  exact physicalPictureGenerated_iff_tag inOld inCore
    (Quotient.mk (Tcore.wagonSetoid μ))
    (Quotient.mk (Told.wagonSetoid μ))
    (fun i s t h => Quotient.sound ((hRel μ i s t).mp (Quotient.exact h))) a b

/-- Different actual wagon classes remain different source labels, even
when their vertex carriers are equal. Unused labels need not be retained. -/
noncomputable def classTag
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
  Told.rel κ (inOld s) (inOld t) ↔
    Tcore.rel κ (inCore i s) (inCore i t)) (μ : Fin (m + 1)) :
    Quotient ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonSetoid μ) ↪
      Quotient (Tcore.wagonSetoid μ) ⊕
        (I × Quotient (Told.wagonSetoid μ)) where
  toFun := fun q => Quotient.liftOn q
    (edgeTag Told Tcore inOld inCore μ)
    (by
      intro a b hab
      exact (rel_iff_edgeTag Told Tcore inOld inCore hShared hRel μ a b).mp hab)
  inj' := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | h a =>
      induction r using Quotient.inductionOn with
      | h b =>
        exact Quotient.sound
          ((rel_iff_edgeTag Told Tcore inOld inCore hShared hRel μ a b).mpr hqr)

/-- The source-label parent allows a private child to acquire a shared parent. -/
noncomputable def parentTag (μ ν : Fin (m + 1)) (hμν : μ ≤ ν) :
    (Quotient (Tcore.wagonSetoid μ) ⊕
      (I × Quotient (Told.wagonSetoid μ))) →
    (Quotient (Tcore.wagonSetoid ν) ⊕
      (I × Quotient (Told.wagonSetoid ν))) :=
  gluedWagonParent
    (contact Told Tcore inOld inCore μ)
    (contact Told Tcore inOld inCore ν)
    (Tcore.wagonParent μ ν hμν) (Told.wagonParent μ ν hμν)

/-- Parent compatibility on every real physical edge. -/
theorem edgeTag_parent
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
  Told.rel κ (inOld s) (inOld t) ↔
    Tcore.rel κ (inCore i s) (inCore i t)) (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (a : PhysicalPictureEdge inOld I CoreEdge) :
    parentTag Told Tcore inOld inCore μ ν hμν
        (edgeTag Told Tcore inOld inCore μ a) =
      edgeTag Told Tcore inOld inCore ν a := by
  cases a with
  | inl b => rfl
  | inr z =>
    exact gluedWagonParent_standard
      (contact Told Tcore inOld inCore μ)
      (contact Told Tcore inOld inCore ν)
      (Tcore.wagonParent μ ν hμν) (Told.wagonParent μ ν hμν)
      (fun i u c hc => sharedWagonQuotient_contact_parent
        Told Tcore μ ν hμν (fun _ : I => inOld) inCore hRel i u c hc)
      z.1 (Quotient.mk (Told.wagonSetoid μ) z.2.1)

/-- The quotient-class identification commutes with every parent map. -/
theorem classTag_parent (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (q : Quotient ((physicalPictureGeneratedTrain
      Told Tcore inOld inCore hShared).wagonSetoid μ)) :
    parentTag Told Tcore inOld inCore μ ν hμν
        (classTag Told Tcore inOld inCore hShared hRel μ q) =
      classTag Told Tcore inOld inCore hShared hRel ν
        ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonParent μ ν hμν q) := by
  induction q using Quotient.inductionOn with
  | h a => exact edgeTag_parent Told Tcore inOld inCore hRel μ ν hμν a

/-- Union of all source edge carriers carrying a specified wagon tag. -/
noncomputable def sourceCarrier
    (oldCarrier : I → OldEdge → Set W)
    (coreCarrier : CoreEdge → Set W) (μ : Fin (m + 1)) :
    (Quotient (Tcore.wagonSetoid μ) ⊕
      (I × Quotient (Told.wagonSetoid μ))) → Set W :=
  GeneratedTaggedWagonCarrier
    (taggedOldFiberCarrier (Quotient.mk (Told.wagonSetoid μ)) oldCarrier)
    (taggedCoreFiberCarrier (Quotient.mk (Tcore.wagonSetoid μ)) coreCarrier)
    (contact Told Tcore inOld inCore μ)

/-- Complete carriers agree on actual wagon classes, not only on edges. -/
theorem classTag_carrier_eq
    (oldCarrier : I → OldEdge → Set W)
    (coreCarrier : CoreEdge → Set W)
    (physicalCarrier : PhysicalPictureEdge inOld I CoreEdge → Set W)
    (hCore : ∀ b, physicalCarrier (physicalCoreEdge inOld I b) = coreCarrier b)
    (hStd : ∀ i a,
      physicalCarrier (physicalStandardEdge inOld inCore i a) = oldCarrier i a)
    (μ : Fin (m + 1))
    (q : Quotient ((physicalPictureGeneratedTrain
      Told Tcore inOld inCore hShared).wagonSetoid μ)) :
    (physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonClassCarrier physicalCarrier μ q =
      sourceCarrier Told Tcore inOld inCore oldCarrier coreCarrier μ
        (classTag Told Tcore inOld inCore hShared hRel μ q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    ext x
    exact physicalPictureGeneratedTrain_wagonCarrier_eq_tagged
      Told Tcore μ inOld inCore hShared (fun i s t => (hRel μ i s t).mp)
      oldCarrier coreCarrier physicalCarrier hCore hStd a x

/-- Transfer the source-label parent bound to the ACTUAL generated train.
The geometric bound is an explicit hypothesis, not a consequence of nesting. -/
theorem parentIntersectionBound
    (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
  Told.rel κ (inOld s) (inOld t) ↔
    Tcore.rel κ (inCore i s) (inCore i t))
    (oldCarrier : I → OldEdge → Set W)
    (coreCarrier : CoreEdge → Set W)
    (physicalCarrier : PhysicalPictureEdge inOld I CoreEdge → Set W)
    (hCore : ∀ b, physicalCarrier (physicalCoreEdge inOld I b) = coreCarrier b)
    (hStd : ∀ i a,
      physicalCarrier (physicalStandardEdge inOld inCore i a) = oldCarrier i a)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν) (allowed : Set W)
    (hBound : TrainParentIntersectionBound
      (sourceCarrier Told Tcore inOld inCore oldCarrier coreCarrier μ)
      (parentTag Told Tcore inOld inCore μ ν hμν) allowed) :
    TrainParentIntersectionBound
      ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonClassCarrier physicalCarrier μ)
      ((physicalPictureGeneratedTrain Told Tcore inOld inCore hShared).wagonParent μ ν hμν) allowed := by
  apply trainParentIntersectionBound_restrict
    (sourceCarrier Told Tcore inOld inCore oldCarrier coreCarrier μ)
    (parentTag Told Tcore inOld inCore μ ν hμν)
    _ _ allowed hBound
    (classTag Told Tcore inOld inCore hShared hRel μ)
    (classTag Told Tcore inOld inCore hShared hRel ν)
  · intro q
    exact classTag_parent Told Tcore inOld inCore hShared hRel μ ν hμν q
  · intro q x hx
    rw [classTag_carrier_eq Told Tcore inOld inCore hShared hRel
      oldCarrier coreCarrier physicalCarrier hCore hStd μ q] at hx
    exact hx

end StructuralRamsey.Girth.PhysicalWagonModel
