import Girth.TrainSingletonFirstCut
import Girth.TrainRecursiveRefinementGlobalCutGirth

set_option autoImplicit false

/-!
# Actual physical girth gain without a bottom-girth premise

This additive version of the actual fine-train girth theorem builds the
refinement from singleton parameters and positive full-system bounds.
The retained first-cut bound is still needed for global localization.
It neither constructs the recursive witness nor removes mixed forests
from the outer picture-step contract.
-/

namespace StructuralRamsey.Girth

universe u v
variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- The actual support gains one girth unit from singleton parameters,
positive inserted system bounds and the retained first-cut system bound.
No bottom girth or forest hypothesis is used. -/
theorem selectedPicture_actualSupport_girthGain_of_singletonSystemCuts
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m)
    (hA : A.Irreducible)
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
    FirstWagonRefinement.ofFineTrain_of_singletonAndPositiveSystemBounds
      A B D C family selected T hm
      C.part firstAllowed g (actualASupport_part_injOn A hA C) permitted
      hSubset hSingleton hParameters hFullPositive
  have hFirstCut : LabelledGirthGT
      ((T.forgetFirstCuts hm).wagonClassCarrier
        (fun edge => edge.1) (⟨1, by omega⟩ : Fin (m + 1))) (g + 1) :=
    selectedPicture_retainedCutGirth_of_fullSystemGirth
      A B D C family selected T hm
      (⟨1, by omega⟩ : Fin (m + 1)) (g + 1)
      hFullRetainedFirst
  exact R.actualSupport_girthGT_of_retainedFirstCut A hA C hg hFirstCut

end StructuralRamsey.Girth
