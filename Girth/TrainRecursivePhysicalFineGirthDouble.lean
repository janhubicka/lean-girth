import Girth.TrainRecursiveRefinementDoubleGirth
import Girth.TrainRecursiveBottomEqualityBridge
import Girth.TrainRecursivePhysicalFineGirthGain

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: true physical coarsened girth from a genuine fine witness

The bottom child bounds follow from the single-part first parameter.
The positive system-cut bounds and the literal retained first cutoff
give the global conclusion. The empty-tail variant uses universality
of the coarsened first wagon.
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

/-- The bottom children lie in a single first wagon. Their edge carriers are
transversal, and the first parameter confines their intersections to one part.
The remaining child bounds come from the positive system cuts. -/
def FirstWagonRefinement.ofFineTrain_of_singletonBottomAndPositiveSystemBounds
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m) (hA : A.Irreducible)
    (firstAllowed : Set P) (g : ℕ)
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
        (firstRefinementChild m d hm j)).FullSystemGirthGT g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) C.part firstAllowed g := by
  apply FirstWagonRefinement.ofFineTrain T hm (fun edge => edge.1) C.part
    firstAllowed g permitted hSubset hSingleton hParameters
  intro j p
  by_cases hZero : j.val = 0
  · have hj : j = (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)) := Fin.ext hZero
    subst j
    apply labelledGirthGT_of_singleton_intersections _ C.part _
      (hSingleton ⟨0, Nat.zero_lt_succ d⟩)
    · intro a
      exact (congrArg (Set.InjOn C.part)
        (congrFun (T.bottom_wagonClassCarrier_eq (fun e => e.val)) a.val)).mpr
        (actualASupport_part_injOn A hA C (T.bottomQuotientEdge a.val))
    · intro a b hab
      exact hParameters _ (fun h => hab (Subtype.ext h))
        (a.property.trans b.property.symm)
  · exact selectedPicture_childGirth_of_fullSystemGirth
      A B D C family selected T
      (firstRefinementChild m d hm j) (firstRefinementParent m d hm j)
      (by change j.val ≤ j.val + 1; omega) p g
      (hFullPositive j (Nat.pos_of_ne_zero hZero))

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
    FirstWagonRefinement.ofFineTrain_of_singletonBottomAndPositiveSystemBounds
      A B D C family selected T hm hA firstAllowed g permitted
      hSubset hSingleton hParameters hFullPositive
  have hFirstCut : LabelledGirthGT
      ((T.forgetFirstCuts hm).wagonClassCarrier
        (fun edge => edge.1) (⟨1, by omega⟩ : Fin (m + 1))) h :=
    selectedPicture_retainedCutGirth_of_fullSystemGirth
      A B D C family selected T hm
      (⟨1, by omega⟩ : Fin (m + 1)) h hFullRetainedFirst
  exact R.actualSupport_girthGT_of_retainedFirstCut_twice
    A hA C hg h hh hFirstCut

/-- Empty-tail variant: the original first wagon is universal. -/
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
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g)
    (hFirstUniversal : ∀ e f : OldACarrierEdge A C.toRelStructure,
      (T.forgetFirstCuts hm).rel ⟨1, by omega⟩ e f) :
    GirthGT (supportCopies A C.toRelStructure) (2 * g + 1) := by
  let R : FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) C.part firstAllowed g :=
    FirstWagonRefinement.ofFineTrain_of_singletonBottomAndPositiveSystemBounds
      A B D C family selected T hm hA firstAllowed g permitted
      hSubset hSingleton hParameters hFullPositive
  exact R.actualSupport_girthGT_of_first_universal_twice
    A hA C hg hFirstUniversal

end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.selectedPicture_actualSupport_girthGain_twice_of_fineSystemCuts
#print axioms StructuralRamsey.Girth.selectedPicture_actualSupport_girthGain_twice_of_firstUniversal
