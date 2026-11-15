import Girth.TrainFillingPrivateCanonicalTwoTypeOldTrain
import Girth.TrainFillingPrivateActualOrderStrictMono
import Girth.TrainFillingPrivateCanonicalCutBridge

set_option Elab.async false

/-!
# All-cut system girth of actual (selected parent, EHN choice) targets

The actual cutoff-two two edge types are distinct:
 Aold : the LARGE ordered edge on the complete vertex set of X,
 Asmall : the ORIGINAL SMALL coloured edge type of each X-edge.

The shorter RR_h supplies an OrderStage for Aold and M.
Its canonical filled target is
  H = N[X] = ofSupportCopies Asmall R (supportCopies Aold N) ...
The earlier one-type OrderStage canonical filling theorem does NOT
apply to this situation; the new two-type bridge does.

This theorem composes, FOR THE SAME ACTUAL H:

1. OrderStage.allCutGirth at the old cut j, including equality zero;
2. the checked generic full-system-girth filling transfer,
   with two INDEPENDENT edge languages;
3. the exact identity of the selected old-edge train with S.train
   for canonical H (no arbitrary transported train);
4. the actual OrderStage selected parent beta_i and its exact range;
5. the actual ordered-carrier selected edge embedding;
6. the checked global designated-subcopy scattering girth transfer
   to the genuine (selected old parent, EHN choice) target family.

In particular no output system girth, old/new edge-type equality,
or deletion of ambient edges is postulated.

Remaining dependencies are the concrete earlier construction of M
from the real covered/marked selected EHN W family, the actual
shorter OrderStage RR_h arrow, and the source T full
partite/predicate/train image.

All code here is a candidate until exact-head Lean compilation.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u0 u1 v

variable {Lold : RelLanguage.{u0}}
variable {Lsmall : RelLanguage.{u1}}
variable {Uold Usmall C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Every restored proper cut of the ACTUAL labelled selected
target family has the old OrderStage system-girth bound,
including the first restored cut coming from OLD equality.
No new girth assumption on H or on the target is used. -/
theorem actualOrderStage_canonicalTwoTypeTargetGirth
    [Nontrivial X] [Finite X]
    [LinearOrder X] [LinearOrder (Vertex U)]
    (Aold : RelStructure Lold Uold) [Nontrivial Uold]
    (M : RelStructure Lold (Vertex U))
    {t : List ℕ}
    (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies Aold M =
      Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure Lold Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage Aold M D family t
      (contractedPhysicalTrain U Aold M T hm hSupport hLinear)
      allowed)
    [PartialOrder S.Vertex]
    (Asmall : RelStructure Lsmall Usmall)
    [Nontrivial Usmall]
    (R : RelStructure Lsmall X)
    (place : OldACarrierEdge Aold S.system.toRelStructure →
      (X ↪ S.Vertex))
    (hRange : ∀ f, Set.range (place f) = f.1)
    (hCovers : ∀ x : X, ∃ a : Embedding Asmall R,
      x ∈ copyCarrier a)
    (hSmallLinear : ALinear Asmall R)
    (hTemplate : ∀ c : C, (U c).templateEdges =
      supportCopies Asmall R)
    (hLocal : ∀ c : C, Nonempty (U c).LocalEdge)
    (hSourceMono : ∀ cp : C × P,
      StrictMono (fun x : X =>
        tagVertex U cp.1 ((U cp.1).place cp.2 x)))
    (hSelectedMono :
      ∀ i : ActualOrderParent U Aold M T hm
        hSupport hLinear D family allowed S,
        StrictMono (fun z : Vertex U =>
          (actualOrderParentVertex U Aold M T hm
            hSupport hLinear D family allowed S i) z))
    (hCanonicalMono :
      ∀ f : OldACarrierEdge Aold S.system.toRelStructure,
        StrictMono (place f))
    (j : Fin t.length) :
    let H : UniformFillingData S.Vertex X :=
      UniformFillingData.ofSupportCopies Asmall R
        (supportCopies Aold S.system.toRelStructure)
        place hRange
        (oldACarrier_edges_inter_subsingleton_of_aLinear
          Aold S.system.toRelStructure S.aLinear)
        hCovers
    let Real := actualOrderStageFaithfulParentwise_of_strictMono
      U Aold M T hm hSupport hLinear D family allowed S
      H (by rfl)
      (by
        intro c
        exact hTemplate c)
      hLocal hSourceMono hSelectedMono hCanonicalMono
      j.castSucc j.isLt
    (Real.toParentwiseRealization.designatedFamily.target).FullSystemGirthGT
      (t.get j) := by
  let H : UniformFillingData S.Vertex X :=
    UniformFillingData.ofSupportCopies Asmall R
      (supportCopies Aold S.system.toRelStructure)
      place hRange
      (oldACarrier_edges_inter_subsingleton_of_aLinear
        Aold S.system.toRelStructure S.aLinear)
      hCovers
  let vertex := actualOrderParentVertex U Aold M T hm
    hSupport hLinear D family allowed S
  let β := actualOrderParentOldEdge U Aold M T hm
    hSupport hLinear D family allowed S H (by rfl)
  let oldTrain := actualSelectedFilledOldTrain U Aold M T hm
    hSupport hLinear D family allowed S.toForestTailStage
    H (by rfl)
  have hCorrectOldTrain : oldTrain = S.train :=
    actualSelectedFilledOldTrain_eq_stage_for_canonicalH
      U Aold M T hm hSupport hLinear D family allowed
      S.toForestTailStage Asmall R place hRange hCovers
  have hTemplateH :
      ∀ c : C, (U c).templateEdges = H.templateEdges := by
    intro c
    exact hTemplate c
  have hFaithful :
      ∀ i : ActualOrderParent U Aold M T hm
        hSupport hLinear D family allowed S,
        ∀ a b : C × P,
          (contractedChoiceTrain U T hm).rel j.castSucc a b ↔
          oldTrain.rel j.castSucc (β i a) (β i b) := by
    intro i a b
    exact actualOrderParentOldEdge_faithful U Aold M T hm
      hSupport hLinear D family allowed S H (by rfl)
      i j.castSucc a b
  have hExactCarriers :
      ∀ i : ActualOrderParent U Aold M T hm
        hSupport hLinear D family allowed S,
        ∀ a : Edge U,
          (selectedIndexedFilledEdgeEmbedding U H hTemplateH
            (β i) a).1 =
            vertex i '' edgeCarrier U a := by
    intro i a
    exact actualOrderParent_filledEdgeCarrier_of_strictMono U
      Aold M T hm hSupport hLinear D family allowed
      S H (by rfl) hTemplateH
      hSourceMono hSelectedMono hCanonicalMono i a
  have hExactOldRange :
      ∀ i : ActualOrderParent U Aold M T hm
        hSupport hLinear D family allowed S,
        Set.range (β i) =
          {f : H.OldEdge | f.1 ⊆ Set.range (vertex i)} :=
    actualOrderParentOldEdge_range_eq_contained U
      Aold M T hm hSupport hLinear D family allowed
      S H (by rfl)
  have hOldGirth :
      (H.toTrainFilling.inheritedCutData S.train
        (fun i : ActualOrderParent U Aold M T hm
          hSupport hLinear D family allowed S =>
          copyCarrier i.1.embedding)
        (fun i : ActualOrderParent U Aold M T hm
          hSupport hLinear D family allowed S =>
          {e : H.OldEdge | e.1 ⊆ copyCarrier i.1.embedding})
        j.castSucc).FullSystemGirthGT (t.get j) := by
    exact S.canonicalFilledCut_fullSystemGirthGT_twoTypes
      Aold M D family Asmall R place hRange hCovers hSmallLinear j
  have hActualOldGirth :
      (H.toTrainFilling.inheritedCutData oldTrain
        (fun i : ActualOrderParent U Aold M T hm
          hSupport hLinear D family allowed S =>
          Set.range (vertex i))
        (fun i : ActualOrderParent U Aold M T hm
          hSupport hLinear D family allowed S =>
          {e : H.OldEdge | e.1 ⊆ Set.range (vertex i)})
        j.castSucc).FullSystemGirthGT (t.get j) := by
    rw [hCorrectOldTrain]
    exact hOldGirth
  exact canonicalFilledSelected_targetFullSystemGirthGT_of_inherited_carrier
    U H hTemplateH vertex β T hm oldTrain
    j.castSucc j.isLt hLocal
    hFaithful hExactCarriers hExactOldRange hActualOldGirth

end StructuralRamsey.Girth.IndexedPrivateChoice
