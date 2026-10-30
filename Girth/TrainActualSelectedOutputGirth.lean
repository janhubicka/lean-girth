import Girth.TrainDesignatedReindexGirth
import Girth.TrainSelectedPictureLabelEquiv
import Girth.TrainSelectedPictureOutputIncidence

set_option Elab.async false

/-!
# Indexed output cycles and the actual selected-copy system agree

The geometric attachment model uses pairs of a standard index and an old
selected copy. The recursive stage uses actual transported selected copies.
For a two-edge target, the checked private-vertex argument gives an exact
equivalence between these types. This identifies the whole incidence record
after designated-label reindexing and hence the full system-girth predicate,
including genuine global simultaneous replacement plans.

Physical linearity does not depend on designated labels and needs no such
nondegeneracy assumption. No output cycle bound is proved from geometry:
the equivalence transfers a bound once the positive-cut argument supplies it.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
  (activeCarrier A C e.toFunctionEmbedding)))
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Attached" => StructuralRamsey.Partite.Attachment.attach C S E f
local notation "NewSelected" => transportedSelectedCopies B D C family selected S E f
local notation "Train" => generatedActualASupportTrain A hA C.toRelStructure S
  E.toRelStructure (fun i => StructuralRamsey.Partite.Embedding.toEmbedding (f i)) T U hShared
local notation "Indexed" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e E.toRelStructure
  (fun i => StructuralRamsey.Partite.Embedding.toEmbedding (f i)) T U hShared μ
local notation "Actual" => selectedPictureOrderOneData A B D Attached family
  NewSelected Train μ

/-- Both output presentations have literally the same physical edge and
wagon linearity. This holds even for a one-edge target or empty selection. -/
theorem attachedSelectedPicture_linearPretrain_iff_actualSelected :
    (Indexed).LinearPretrain ↔ (Actual).LinearPretrain := Iff.rfl

variable [Finite UA]
variable (hStrong : ∀ q : {q : DesignatedCopy B D C family // q ∈ selected},
  AStrong A D (copyCarrier q.1.base))
variable (hTwo : ∀ q : {q : DesignatedCopy B D C family // q ∈ selected},
  ∃ r s : OldACarrierEdge A C.toRelStructure, r ≠ s ∧
  r.1 ⊆ copyCarrier q.1.embedding ∧ s.1 ⊆ copyCarrier q.1.embedding)

/-- Equality of the entire incidence records after the genuine selected
label equivalence: every physical edge and its parent is retained. -/
theorem attachedSelectedPicture_eq_reindex_actualSelected :
    Indexed = (Actual).reindexDesignated
      (transportedSelectedCopyEquiv A B D C family selected e E f hStrong hTwo) := by
  unfold attachedSelectedPictureOrderOneData selectedPictureOrderOneData
    OrderOneData.reindexDesignated
  congr 1
  · funext iq
    exact (transportedSelectedCopyLabel_carrier B D C family selected S E f iq).symm
  · funext iq
    exact congrArg
      (fun Z => {a : OldACarrierEdge A (Attached).toRelStructure | a.1 ⊆ Z})
      (transportedSelectedCopyLabel_carrier B D C family selected S E f iq).symm

include hStrong hTwo in
/-- The indexed and actual selected-copy systems have exactly the same
full system girth at every cutoff. In particular, global plan legality is
preserved; the map does not identify copies merely by their carriers. -/
theorem attachedSelectedPicture_fullSystemGirth_iff_actualSelected (q : ℕ) :
    (Indexed).FullSystemGirthGT q ↔ (Actual).FullSystemGirthGT q := by
  rw [attachedSelectedPicture_eq_reindex_actualSelected
    A hA B D C family selected e E f T U hShared μ hStrong hTwo]
  exact (Actual).reindexDesignated_fullSystemGirth_iff _ q

include hStrong in
/-- The target's two distinct physical A-copies supply the nondegeneracy
input uniformly, so no separate witnesses are needed for selected copies. -/
theorem attachedSelectedPicture_fullSystemGirth_iff_actualSelected_of_target
    (a b : Embedding A B) (hne : ¬ SameCopy a b) (q : ℕ) :
    (Indexed).FullSystemGirthGT q ↔ (Actual).FullSystemGirthGT q := by
  exact attachedSelectedPicture_fullSystemGirth_iff_actualSelected
    A hA B D C family selected e E f T U hShared μ hStrong
    (fun s => selectedCopy_two_edges_of_target A B D C family selected s a b hne) q

end StructuralRamsey.Girth
