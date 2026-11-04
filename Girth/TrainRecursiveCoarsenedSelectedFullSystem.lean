import Girth.TrainRecursiveSelectedGluingIncidence
import Girth.TrainRecursiveWitnessPass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Positive full-system girth through an exact selected-label equivalence

The genuine lower ForestTailStage supplies positive full-system girth
for its complete selected-picture incidence system at every positive
stage cut. The actual gluing interface may index its copies by a
different type, so the ONLY extra information required to transfer
this certificate is an honest equivalence of labels and pointwise
equality of their complete physical carriers.

The already verified activeGluingWitness_fullSystemGirth_iff_selectedPicture
compares the WHOLE simultaneous-replacement incidence structures,
including all ambient physical A-support edges and full quotient wagon
labels, not just ordinary Berge cycles.

For the canonical coarsened selected family the equivalence is literally
identity and carrier equality follows from the partite embedding's
unchanged relational map. Those are separate geometry facts, not
postulated here. This theorem does not construct a lower recursive
stage or the attached output SupremeCycleBound.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P Q X I : Type v}

variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)

local notation "Source" =>
  Old.toRelStructure.induce (activeCarrier A Old α)

variable (D : RelStructure L Q)
variable {family : Set (Embedding Source D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A Source) t.length}
variable {allowed : Fin (t.length + 1) → Set Q}
variable (S : ForestTailStage A Source D family t targetTrain allowed)

variable (f : I → Embedding Source S.system.toRelStructure)
variable (e : I ≃ {b : DesignatedCopy Source D S.system family //
  b ∈ S.selected})
variable (hCarrier : ∀ i : I,
  copyCarrier (f i) = copyCarrier (e i).1.embedding)

/-- Every positive FULL selected-system-girth certificate passes to
the actual gluing family with the same physical carriers and an
honest bijection of designated indices. This includes simultaneous
replacement plans; no quotient by equal image carriers occurs. -/
theorem ForestTailStage.selectedGluing_fullSystem_at_positive
    (j : Fin t.length) (hj : 0 < j.val) :
    (activeGluingWitnessOrderOneData A Old α
      S.system.toRelStructure f S.train j.castSucc).FullSystemGirthGT
        (t.get j) := by
  exact (activeGluingWitness_fullSystemGirth_iff_selectedPicture
    A Source D Old S.system family S.selected α f S.train
    j.castSucc e hCarrier (t.get j)).mpr
    (S.tailGirth j hj)

/-- A positive stage certificate also gives every numerically
smaller full-system cutoff, with all gluing and physical labels
retained literally. -/
theorem ForestTailStage.selectedGluing_fullSystem_at_positive_mono
    (j : Fin t.length) (hj : 0 < j.val)
    (q : ℕ) (hq : q ≤ t.get j) :
    (activeGluingWitnessOrderOneData A Old α
      S.system.toRelStructure f S.train j.castSucc).FullSystemGirthGT q := by
  have hFull :
      (activeGluingWitnessOrderOneData A Old α
        S.system.toRelStructure f S.train j.castSucc).FullSystemGirthGT
          (t.get j) :=
    S.selectedGluing_fullSystem_at_positive A Old α D f e hCarrier j hj
  refine ⟨hFull.1, ?_⟩
  intro n K hAccept hOrder
  exact hFull.2 n K hAccept (by omega)

end StructuralRamsey.Girth.TrainRecursiveWitness
