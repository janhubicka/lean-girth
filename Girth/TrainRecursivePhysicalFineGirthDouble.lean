import Girth.TrainRecursiveRefinementDoubleGirth
import Girth.TrainRecursivePhysicalFineGirthGain

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: true physical coarsened girth from a genuine fine witness

UNCHECKED CANDIDATE. This is an adapter, not construction of a Ramsey
witness or verification of a lower ForestTailStage. It strengthens the
existing conditional physical girth-gain theorem at exactly the SAME
fine bottom, positive system-cut and parameter interfaces.

No cut is pruned, no child labels are identified, and the retained
first cutoff h is NOT weakened to g+1. The empty-tail alternative
requires an explicitly universal coarsened first wagon.
-/

namespace StructuralRamsey.Girth

universe u v

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA)
variable (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- Physical A-support girth >min(2*g+1,h) from the actual fine train.
Every positive inserted system-girth certificate and the retained
positive original first-cut certificate is still an EXPLICIT input. -/
theorem selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m) (hA : A.Irreducible)
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
    (hBottom : LabelledGirthGT
      (T.wagonClassCarrier (fun edge => edge.1)
        (firstRefinementChild m d hm
          (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))) g)
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g)
    (h : ℕ) (hh : 2 ≤ h)
    (hFullRetainedFirst :
      (selectedPictureOrderOneData A B D C family selected T
        (EdgeTrainLevels.firstForgetIndex m d
          (⟨1, by omega⟩ : Fin (m + 1)))).FullSystemGirthGT h) :
    GirthGT (supportCopies A C.toRelStructure) (min (2 * g + 1) h) := by
  let R : FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) C.part firstAllowed g :=
    FirstWagonRefinement.ofFineTrain_of_bottomAndPositiveSystemBounds
      A B D C family selected T hm C.part firstAllowed g permitted
      hSubset hSingleton hParameters hBottom hFullPositive
  have hFirstCut : LabelledGirthGT
      ((T.forgetFirstCuts hm).wagonClassCarrier
        (fun edge => edge.1) (⟨1, by omega⟩ : Fin (m + 1))) h :=
    selectedPicture_retainedCutGirth_of_fullSystemGirth
      A B D C family selected T hm
      (⟨1, by omega⟩ : Fin (m + 1)) h hFullRetainedFirst
  exact R.actualSupport_girthGT_of_retainedFirstCut_twice
    A hA C hg h hh hFirstCut

/-- Empty-tail variant: all source edges are in the original
first wagon, so no retained-first-cut certificate is needed.
Other inserted full-system and bottom inputs remain explicit. -/
theorem selectedPicture_actualSupport_girthGain_twice_of_firstUniversal
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m) (hA : A.Irreducible)
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
    (hBottom : LabelledGirthGT
      (T.wagonClassCarrier (fun edge => edge.1)
        (firstRefinementChild m d hm
          (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))) g)
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g)
    (hFirstUniversal : ∀ e f : OldACarrierEdge A C.toRelStructure,
      (T.forgetFirstCuts hm).rel ⟨1, by omega⟩ e f) :
    GirthGT (supportCopies A C.toRelStructure) (2 * g + 1) := by
  let R : FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) C.part firstAllowed g :=
    FirstWagonRefinement.ofFineTrain_of_bottomAndPositiveSystemBounds
      A B D C family selected T hm C.part firstAllowed g permitted
      hSubset hSingleton hParameters hBottom hFullPositive
  exact R.actualSupport_girthGT_of_first_universal_twice
    A hA C hg hFirstUniversal

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts
#print axioms StructuralRamsey.Girth.selectedPicture_actualSupport_girthGain_twice_of_firstUniversal
