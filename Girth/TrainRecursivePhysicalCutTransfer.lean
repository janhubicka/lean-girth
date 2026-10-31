import Girth.TrainSystemCutGirthFullConverse
import Girth.TrainRecursiveInitialTailGirth
import Girth.TrainRecursiveRefinementForget

/-!
# From actual full-system bounds to the physical refinement's child cuts

The universal system-girth to labelled-cut theorem was proved for the
complete wagon carriers of an OrderOneData incidence record. This
module identifies those labels with the ACTUAL quotient wagon labels
of a physical support train. No physical edge is pruned, no equal
carrier labels are collapsed, and the index of a child at any parent
is the literal subtype of the actual quotient labels.

Consequently full-system girth at every inserted child cut is enough
for the labelled child-girth hypotheses of FirstWagonRefinement.ofFineTrain.
The separate parent intersection parameters and the geometric
construction of a nontrivial picture step remain explicit inputs.

Only circulation results are used; no appendix axioms or hypotheses.
-/

namespace StructuralRamsey.Girth

universe u v

section LabelledChild

variable {E W : Type v}

/-- A complete labelled cut bound immediately restricts to the
actual children of a chosen parent at a coarser cut.  The child labels
are subtypes of the ORIGINAL quotient labels, not sets of carriers. -/
theorem EdgeTrainLevels.labelledChildGirth_of_labelledCut
    {m : ℕ} (T : EdgeTrainLevels E m) (edge : E → Set W)
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (p : Quotient (T.wagonSetoid ν)) (g : ℕ)
    (hCut : LabelledGirthGT (T.wagonClassCarrier edge μ) g) :
    LabelledGirthGT
      (fun a : {a : Quotient (T.wagonSetoid μ) //
          T.wagonParent μ ν hμν a = p} =>
        T.wagonClassCarrier edge μ a.val) g := by
  exact labelledGirthGT_of_injective_reindex
    (T.wagonClassCarrier edge μ)
    (fun a : {a : Quotient (T.wagonSetoid μ) //
      T.wagonParent μ ν hμν a = p} => a.val)
    (by
      intro a b h
      exact Subtype.ext h)
    g hCut

end LabelledChild

section SelectedActual

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)

/-- The general complete-wagon theorem applies to the ACTUAL
physical train cut.  The quotient-labelled carrier is identified by
the existing exact two-way membership theorem; not even an injective
reindexing of the wagon sort is needed. -/
theorem selectedPicture_labelledCutGirth_of_fullSystemGirth
    (μ : Fin (m + 1)) (q : ℕ)
    (hFull :
      (selectedPictureOrderOneData A B D C family selected T μ).FullSystemGirthGT q) :
    LabelledGirthGT
      (T.wagonClassCarrier (fun edge => edge.1) μ) q := by
  let O := selectedPictureOrderOneData A B D C family selected T μ
  have hWagons :
      LabelledGirthGT (fun p : Quotient (T.wagonSetoid μ) =>
        {x : X | O.WagonVertex p x}) q :=
    O.fullSystemGirth_implies_labelledWagonCutGirth q hFull
  have hCarrier :
      (fun p : Quotient (T.wagonSetoid μ) =>
        {x : X | O.WagonVertex p x}) =
        T.wagonClassCarrier (fun edge => edge.1) μ := by
    funext p
    ext x
    exact selectedPicture_wagonVertex_iff
      A B D C family selected T μ p x
  rw [← hCarrier]
  exact hWagons

/-- Every actual parent-child family at a finer physical level has
labelled girth above q whenever the complete incidence system of
that finer level satisfies FullSystemGirthGT q. -/
theorem selectedPicture_childGirth_of_fullSystemGirth
    (μ ν : Fin (m + 1)) (hμν : μ ≤ ν)
    (p : Quotient (T.wagonSetoid ν)) (q : ℕ)
    (hFull :
      (selectedPictureOrderOneData A B D C family selected T μ).FullSystemGirthGT q) :
    LabelledGirthGT
      (fun a : {a : Quotient (T.wagonSetoid μ) //
          T.wagonParent μ ν hμν a = p} =>
        T.wagonClassCarrier (fun edge => edge.1) μ a.val) q := by
  exact T.labelledChildGirth_of_labelledCut
    (fun edge => edge.1) μ ν hμν p q
    (selectedPicture_labelledCutGirth_of_fullSystemGirth
      A B D C family selected T μ q hFull)

end SelectedActual

section ConcreteRefinement

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- Construct the actual full first-wagon refinement record from
system-girth bounds at its inserted physical child coordinates.
Its parent-intersection parameter geometry remains a genuine input,
but ALL labelled child girth hypotheses are derived, not assumed. -/
def FirstWagonRefinement.ofFineTrain_of_physicalSystemBounds
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
    (hFull : ∀ j : Fin (d + 1),
      (selectedPictureOrderOneData A B D C family selected T
        (firstRefinementChild m d hm j)).FullSystemGirthGT g) :
    FirstWagonRefinement (T.forgetFirstCuts hm) hm
      (fun edge => edge.1) part firstAllowed g :=
  FirstWagonRefinement.ofFineTrain
    T hm (fun edge => edge.1) part firstAllowed g
    permitted hSubset hSingleton hParameters
    (fun j p =>
      selectedPicture_childGirth_of_fullSystemGirth
        A B D C family selected T
        (firstRefinementChild m d hm j)
        (firstRefinementParent m d hm j)
        (by change j.val ≤ j.val + 1; omega)
        p g (hFull j))

end ConcreteRefinement


section RetainedCut

variable {E W : Type v}

/-- Forgetting inserted first levels changes neither the complete
retained labelled cut family nor its girth. The exact quotient
equivalence keeps distinct wagon labels distinct even if their
physical carriers coincide. Level zero is retained as zero. -/
theorem EdgeTrainLevels.labelledRetainedCutGirth_of_fine
    {m d : ℕ} (T : EdgeTrainLevels E (m + d)) (hm : 0 < m)
    (edge : E → Set W) (μ : Fin (m + 1)) (q : ℕ)
    (hFine : LabelledGirthGT
      (T.wagonClassCarrier edge (firstForgetIndex m d μ)) q) :
    LabelledGirthGT
      ((T.forgetFirstCuts hm).wagonClassCarrier edge μ) q := by
  have hEq :
      (T.forgetFirstCuts hm).wagonClassCarrier edge μ =
        fun p => T.wagonClassCarrier edge (firstForgetIndex m d μ)
          (T.forgetFirstCuts_wagonEquiv hm μ p) := by
    funext p
    exact T.forgetFirstCuts_wagonClassCarrier hm edge μ p
  rw [hEq]
  exact labelledGirthGT_of_injective_reindex
    (T.wagonClassCarrier edge (firstForgetIndex m d μ))
    (T.forgetFirstCuts_wagonEquiv hm μ)
    (T.forgetFirstCuts_wagonEquiv hm μ).injective q hFine

end RetainedCut

section SelectedRetainedActual

variable {L : RelLanguage.{u}} {UA VB P X : Type v}
variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))

/-- A complete physical system-girth bound at the corresponding
FINE level gives the genuine labelled girth of an original RETAINED
train cut after forgetting extra refinement levels. Every parent
label, ambient support edge and physical vertex carrier is preserved. -/
theorem selectedPicture_retainedCutGirth_of_fullSystemGirth
    {m d : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) (m + d))
    (hm : 0 < m) (μ : Fin (m + 1)) (q : ℕ)
    (hFull : (selectedPictureOrderOneData A B D C family selected T
      (firstForgetIndex m d μ)).FullSystemGirthGT q) :
    LabelledGirthGT
      ((T.forgetFirstCuts hm).wagonClassCarrier
        (fun edge => edge.1) μ) q := by
  exact T.labelledRetainedCutGirth_of_fine hm
    (fun edge => edge.1) μ q
    (selectedPicture_labelledCutGirth_of_fullSystemGirth
      A B D C family selected T (firstForgetIndex m d μ) q hFull)

end SelectedRetainedActual

end StructuralRamsey.Girth
