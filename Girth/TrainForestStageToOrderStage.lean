import Girth.TrainRecursiveWitnessPass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Forest stage to order stage: add only the missing bottom bound

The actual finite Ramsey picture pass already stores all positive
system-girth coordinates in its ForestTailStage.tailGirth field.
OrderStage extends this structure by full system-girth at every
requested cut. For any NONEMPTY cutoff vector q :: h, the only
additional datum required is full bottom system-girth >q.

No separate top-cut system girth, reconstruction of the train,
reindexing of selected embeddings or additional Ramsey arrow is used.
This is the final structural packaging in the F_t -> R_t conversion.
The remaining hard input is constructing the bottom bound at the end
of the finite picture pass and preserving the selected Ramsey family.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (RelStructure.Embedding B D)}
variable {q : ℕ} {h : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: h).length}
variable {allowed : Fin ((q :: h).length + 1) → Set P}

/-- An actual finite forest stage with the SAME q bottom full-system
bound is already an order-stage witness. Its selected subfamily,
physical edges, train, adjacent parameters, forest invariant and all
tail coordinates are literally the existing fields, unchanged. -/
noncomputable def ForestTailStage.withBottomSystemGirth
    (S : ForestTailStage A B D family (q :: h) targetTrain allowed)
    (hBottom :
      (selectedPictureOrderOneData A B D S.system family S.selected
        S.train (⟨0, by simp⟩ : Fin ((q :: h).length + 1))).FullSystemGirthGT q) :
    OrderStage A B D family (q :: h) targetTrain allowed := by
  refine { toForestTailStage := S, allCutGirth := ?_ }
  intro j
  by_cases hj : j.val = 0
  · have hIndex : j =
        (⟨0, by simp⟩ : Fin (q :: h).length) := Fin.ext hj
    subst j
    simpa using hBottom
  · exact S.tailGirth j (by omega)

/-- Converting the forest stage changes no mathematical data:
the underlying forest stage is definitionally the original one. -/
@[simp] theorem ForestTailStage.withBottomSystemGirth_forget
    (S : ForestTailStage A B D family (q :: h) targetTrain allowed)
    (hBottom :
      (selectedPictureOrderOneData A B D S.system family S.selected
        S.train (⟨0, by simp⟩ : Fin ((q :: h).length + 1))).FullSystemGirthGT q) :
    (S.withBottomSystemGirth hBottom).toForestTailStage = S := rfl

end StructuralRamsey.Girth.TrainRecursiveWitness
