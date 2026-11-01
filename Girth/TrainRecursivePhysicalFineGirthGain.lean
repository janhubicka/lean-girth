import Girth.TrainRecursiveRefinementGlobalCutGirth
import Girth.TrainRecursiveMixedBottomRefinement
import Girth.TrainRecursivePhysicalCutTransfer

set_option autoImplicit false

/-!
# Complete physical girth gain from named fine-train certificates

For the q=g+1 > 2 step of the circulation induction, the actual fine
physical support train needs three kinds of certificates:
* bottom labelled physical equality-cut girth >g;
* full system girth >g at each *positive* inserted child coordinate;
* full system girth >g+1 at the fine coordinate retaining the ORIGINAL
  first wagon relation (the first nonempty-tail cut).

From these certificates and the sibling-intersection geometry, build the
actual first-wagon refinement, transfer the retained cut by its exact
quotient equivalence, and apply global localization and girth gain.
No assumptions of universal first wagons, pruning or artificial edge
carriers occur.  Crucially, this theorem does NOT produce the required
fine-train certificates: those are supplied by the local recursive
witness and remain a separate construction obligation.
-/

namespace StructuralRamsey.Girth

universe u v

section ActualFine

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- The induction's complete q=g+1 ordinary girth gain, for the
ACTUAL fine physical support and exact retained first-wagon quotient,
provided its named bottom, positive and retained certificates. -/
include hA

theorem selectedPicture_actualSupport_girthGain_of_fineSystemCuts
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m)
    (firstAllowed : Set P) (g : ℕ) (hg : 2 ≤ g)
    (permitted : Fin (d + 1) → Set P)
    (hSubset : ∀ j, permitted j ⊆ firstAllowed)
    (hSingleton : ∀ j, (permitted j).Subsingleton)
    (hParameters : ∀ j : Fin (d + 1),
      TrainParentIntersectionBound
        (T.wagonClassCarrier (fun edge => edge.1)
          (firstRefinementChild m d hm j))
        (T.wagonParent (firstRefinementChild m d hm j)
          (firstRefinementParent m d hm j)
          (by change j.val ≤ j.val + 1; omega))
        (C.part ⁻¹' permitted j))
    (hBottom :
      LabelledGirthGT
        (T.wagonClassCarrier (fun edge => edge.1)
          (firstRefinementChild m d hm
            (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))) g)
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g)
    (hFullRetainedFirst :
      (selectedPictureOrderOneData A B D C family selected T
        (EdgeTrainLevels.firstForgetIndex m d
          (⟨1, by omega⟩ : Fin (m + 1)))).FullSystemGirthGT (g + 1)) :
    GirthGT (supportCopies A C.toRelStructure) (g + 1) := by
  let R : FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) C.part firstAllowed g :=
    FirstWagonRefinement.ofFineTrain_of_bottomAndPositiveSystemBounds
      A B D C family selected T hm
      C.part firstAllowed g permitted
      hSubset hSingleton hParameters hBottom hFullPositive
  have hFirstCut : LabelledGirthGT
      ((T.forgetFirstCuts hm).wagonClassCarrier
        (fun edge => edge.1) (⟨1, by omega⟩ : Fin (m + 1))) (g + 1) :=
    selectedPicture_retainedCutGirth_of_fullSystemGirth
      A B D C family selected T hm
      (⟨1, by omega⟩ : Fin (m + 1)) (g + 1)
      hFullRetainedFirst
  exact R.actualSupport_girthGT_of_retainedFirstCut A hA C hg hFirstCut

end ActualFine

end StructuralRamsey.Girth
