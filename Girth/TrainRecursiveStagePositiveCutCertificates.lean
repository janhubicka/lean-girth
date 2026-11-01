import Girth.TrainRecursivePhysicalCutTransfer
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false

/-!
# Exact physical cut certificates already stored in a forest-tail stage

A genuine ForestTailStage stores FullSystemGirthGT at every positive tail
coordinate. This module exposes that field with a lowered cutoff, and
derives complete labelled wagon-cut and parent-child girth certificates
for the actual physical train. In particular these are not assumptions
about a new phantom carrier family or an arbitrary projected B-lift.

All labels are genuine quotient classes of actual A-support edges.
The theorem does not claim construction of the recursive local witness,
a first-refinement record, or the positive-cut supreme certificates
in the attachment that are needed to produce a new ForestTailStage.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A : RelStructure L UA) (B : RelStructure L VB)
variable (D : RelStructure L P)
variable (family : Set (RelStructure.Embedding B D))
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- The actual selected-picture full system-girth bound stored in a
ForestTailStage may be lowered at any positive tail coordinate.
The same actual pretrain and selected labels are retained. -/
theorem ForestTailStage.fullSystemGirth_at_positive
    (S : ForestTailStage A B D family t targetTrain allowed)
    (j : Fin t.length) (hj : 0 < j.val)
    (q : ℕ) (hq : q ≤ t.get j) :
    (selectedPictureOrderOneData A B D S.system family S.selected
      S.train j.castSucc).FullSystemGirthGT q := by
  have hFull := S.tailGirth j hj
  refine ⟨hFull.1, ?_⟩
  intro n K hAccept hOrder
  exact hFull.2 n K hAccept (by omega)

/-- The full labelled quotient-wagon family of the genuine stage at any
positive tail coordinate inherits its requested cutoff from the stage's
indexed FullSystemGirthGT certificate. -/
theorem ForestTailStage.labelledPhysicalCutGirth_at_positive
    (S : ForestTailStage A B D family t targetTrain allowed)
    (j : Fin t.length) (hj : 0 < j.val)
    (q : ℕ) (hq : q ≤ t.get j) :
    LabelledGirthGT
      (S.train.wagonClassCarrier (fun edge => edge.1) j.castSucc) q := by
  exact selectedPicture_labelledCutGirth_of_fullSystemGirth
    A B D S.system family S.selected S.train j.castSucc q
    (ForestTailStage.fullSystemGirth_at_positive A B D family S j hj q hq)

/-- Child-girth in any actual fixed parent of the stage's positive
tail cut.  The family of children is the subtype of true quotient
labels with that exact parent, without identifying equal carriers. -/
theorem ForestTailStage.labelledPhysicalChildGirth_at_positive
    (S : ForestTailStage A B D family t targetTrain allowed)
    (j : Fin t.length) (hj : 0 < j.val)
    (ν : Fin (t.length + 1)) (hμν : j.castSucc ≤ ν)
    (p : Quotient (S.train.wagonSetoid ν))
    (q : ℕ) (hq : q ≤ t.get j) :
    LabelledGirthGT
      (fun a : {a : Quotient (S.train.wagonSetoid j.castSucc) //
          S.train.wagonParent j.castSucc ν hμν a = p} =>
        S.train.wagonClassCarrier (fun edge => edge.1)
          j.castSucc a.val) q := by
  exact S.train.labelledChildGirth_of_labelledCut
    (fun edge => edge.1) j.castSucc ν hμν p q
    (ForestTailStage.labelledPhysicalCutGirth_at_positive A B D family S j hj q hq)

end StructuralRamsey.Girth.TrainRecursiveWitness
