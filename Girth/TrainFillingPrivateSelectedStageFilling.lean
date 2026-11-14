import Girth.TrainFillingPrivateStageSelectedPhysical
import Girth.TrainFillingRelationalSelectedSupport
import Girth.TrainFillingIndexedActualRestoredParents

set_option Elab.async false

/-!
# The selected lower-stage M-copy in the *actual* uniform filling

The lower recursive stage is over the real relational M, whose
physical A-support edges are exactly the contracted first wagons.
The canonical filling H of its output N has old edges equal to the
FULL A-support of N, not a separately chosen subfamily.

This file constructs the actual selected old-edge injection
  beta : (choice, first wagon) -> H.OldEdge
from the selected b : M -> N, preserving the complete edge carrier.
It then transports N's genuine train along the equality of those
physical support-edge types. The earlier checked targetRestriction
proves the exact proper-cut and top-cut relation equivalence under
this SAME beta. No abstract beta or output train faithfulness is
assumed.

The next step is to use the verified restored-wagon reconstruction
from this pair and to build the global parentwise realization.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Canonical equality-of-support transport between the actual
old edges of a uniform filling and the entire A-support of the
lower-stage selected N. It is an equivalence of complete physical
edge carriers, with no quotient of occurrence labels. -/
noncomputable def actualFilledOldEdgeEquiv
    {N : Type v}
    (A : RelStructure L UA)
    (R : RelStructure L N)
    (H : UniformFillingData N X)
    (hOld : H.oldEdges = supportCopies A R) :
    H.OldEdge ≃ OldACarrierEdge A R where
  toFun e := ⟨e.1, by
    rw [← hOld]
    exact e.2⟩
  invFun e := ⟨e.1, by
    rw [hOld]
    exact e.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    rfl
  right_inv := by
    intro e
    apply Subtype.ext
    rfl

/-- The actual selected b defines every old N edge in the
contracted copy. This map has the complete old-edge carrier,
without any assumed output copy-edge equality. -/
noncomputable def actualSelectedFilledOldEdgeEmbedding [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    (C × P) ↪ H.OldEdge where
  toFun := fun cp =>
    H.selectedSupportOldEdgeEmbedding A M
      S.system.toRelStructure b.embedding hOld
      (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp)
  inj' := by
    intro e f hef
    have hActual :
        contractedPhysicalEdgeEquiv U A M hSupport hLinear e =
          contractedPhysicalEdgeEquiv U A M hSupport hLinear f :=
      (H.selectedSupportOldEdgeEmbedding A M
        S.system.toRelStructure b.embedding hOld).injective hef
    exact (contractedPhysicalEdgeEquiv U A M hSupport hLinear).injective hActual

/-- Every selected old edge is literally the image of its entire
source first-wagon carrier, not just a subset thereof. -/
theorem actualSelectedFilledOldEdgeEmbedding_carrier [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (cp : C × P) :
    (actualSelectedFilledOldEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S b H hOld cp).1 =
        b.embedding.toFunctionEmbedding '' contractedCarrier U cp := by
  change
    (H.selectedSupportOldEdgeEmbedding A M
      S.system.toRelStructure b.embedding hOld
      (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp)).1 =
        b.embedding.toFunctionEmbedding '' contractedCarrier U cp
  rw [H.selectedSupportOldEdgeEmbedding_carrier]
  rw [contractedPhysicalEdgeEquiv_carrier]

/-- The shorter witness's train transported to the actual H old
edge type, without requiring H's old edges to be a restricted family. -/
noncomputable def actualSelectedFilledOldTrain [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure) :
    EdgeTrainLevels H.OldEdge t.length :=
  S.train.restrict
    (actualFilledOldEdgeEquiv (X := X) A S.system.toRelStructure H hOld).toEmbedding

/-- For a selected b, the SAME constructed old-edge injection is
faithful at ALL cuts of the actual old H train. This discharges the
faithfulness premise of the restored-wagon embedding constructor. -/
theorem actualSelectedFilledOldTrain_faithful [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family) (hb : b ∈ S.selected)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (μ : Fin (t.length + 1)) (e f : C × P) :
    (contractedChoiceTrain U T hm).rel μ e f ↔
      (actualSelectedFilledOldTrain U A M T hm hSupport hLinear
        D family allowed S H hOld).rel μ
        (actualSelectedFilledOldEdgeEmbedding U A M T hm
          hSupport hLinear D family allowed S b H hOld e)
        (actualSelectedFilledOldEdgeEmbedding U A M T hm
          hSupport hLinear D family allowed S b H hOld f) := by
  let φ := actualFilledOldEdgeEquiv (X := X)
    A S.system.toRelStructure H hOld
  let β := actualSelectedFilledOldEdgeEmbedding U A M T hm
    hSupport hLinear D family allowed S b H hOld
  have hCast (cp : C × P) :
      φ (β cp) =
        selectedActualMPhysicalEdgeEmbedding U A M T hm
          hSupport hLinear D family allowed S b cp := by
    apply Subtype.ext
    exact (actualSelectedFilledOldEdgeEmbedding_carrier U A M T hm
      hSupport hLinear D family allowed S b H hOld cp).trans
      (stageSelectedActualMPhysicalEdge_carrier U A M T hm
        hSupport hLinear D family allowed S b cp).symm
  change (contractedChoiceTrain U T hm).rel μ e f ↔
    S.train.rel μ (φ (β e)) (φ (β f))
  rw [hCast e, hCast f]
  exact (selectedActualMPhysicalEdgeEmbedding_train_iff U A M T hm
    hSupport hLinear D family allowed S b hb μ e f).symm

end StructuralRamsey.Girth.IndexedPrivateChoice
