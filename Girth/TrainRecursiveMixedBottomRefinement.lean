import Girth.TrainRecursivePhysicalCutTransfer

/-!
# The induction-shaped child-girth premise: bottom plus positive cuts

The actual recursive train does not necessarily carry a system-girth
certificate at bottom equality level zero. Its genuine forest invariant
instead supplies bottom physical Berge girth. For every positive
inserted cut, a full system-girth witness supplies the labelled bound
by the verified universal system-to-cut theorem.

This module builds the FIRST-WAGON refinement record from precisely
that split: one bottom labelled-girth premise and full system bounds
at all other inserted child levels. It does not assume system girth
at bottom, new ambient physical edges, or a completed PictureStep.
The positive parent intersection bounds remain actual geometric input.
-/

namespace StructuralRamsey.Girth

universe u v

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- The exact finite first-wagon refinement needs no bottom
FullSystemGirthGT: bottom labelled girth is sufficient, and proper
inserted cut bounds follow from their actual full-system certificates.

Each child's label is the original quotient wagon label with its
literal parent equation, so coincidence of carriers is never used. -/
def FirstWagonRefinement.ofFineTrain_of_bottomAndPositiveSystemBounds
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m)
    (part : X → P) (firstAllowed : Set P) (g : ℕ)
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
        (part ⁻¹' permitted j))
    (hBottom :
      LabelledGirthGT
        (T.wagonClassCarrier (fun edge => edge.1)
          (firstRefinementChild m d hm
            (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))) g)
    (hFullPositive : ∀ j : Fin (d + 1), 0 < j.val →
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) part firstAllowed g := by
  apply FirstWagonRefinement.ofFineTrain
    T hm (fun edge => edge.1) part firstAllowed g
    permitted hSubset hSingleton hParameters
  intro j p
  by_cases hZero : j.val = 0
  · have hz : j = (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)) :=
      Fin.ext hZero
    subst j
    exact T.labelledChildGirth_of_labelledCut
      (fun edge => edge.1)
      (firstRefinementChild m d hm (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))
      (firstRefinementParent m d hm (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)))
      (by change 0 ≤ 0 + 1; omega) p g hBottom
  · have hPos : 0 < j.val := Nat.pos_of_ne_zero hZero
    exact selectedPicture_childGirth_of_fullSystemGirth
      A B D C family selected T
      (firstRefinementChild m d hm j)
      (firstRefinementParent m d hm j)
      (by change j.val ≤ j.val + 1; omega)
      p g (hFullPositive j hPos)

end StructuralRamsey.Girth
