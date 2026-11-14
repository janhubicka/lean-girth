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


/-- The existing finite train-picture Ramsey pass produces an
OrderStage, provided its terminal readiness invariant supplies
the bottom full-system bound. Positive system-girth, original target
restriction, selected-copy strongness, full train parameters and
foresthood are ALL carried by the unchanged ForestTailStage.

This is an explicit assembly criterion, NOT an assumption that
an arbitrary forest stage already has bottom system girth: the
terminal readiness-to-bottom implication is a genuine remaining
proof obligation for the same-vector conversion. -/
theorem ForestTailStage.ramseyOrderPass_of_ready_bottom
    (S : ForestTailStage A B D family (q :: h) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type v) [Nonempty κ]
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family (q :: h) targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ a : DesignatedCopy B D S.system family,
        a ∈ S.selected ∧ a.base = b)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family (q :: h) targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestTailStage A B D family (q :: h) targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ)
    (hTerminalBottom :
      ∀ T : ForestTailStage A B D family (q :: h) targetTrain allowed,
        Ready [] T →
        (selectedPictureOrderOneData A B D T.system family T.selected
          T.train (⟨0, by simp⟩ : Fin ((q :: h).length + 1))).FullSystemGirthGT q) :
    ∃ T : OrderStage A B D family (q :: h) targetTrain allowed,
      Ready [] T.toForestTailStage ∧
      DesignatedArrow T.toForestTailStage κ := by
  obtain ⟨R, hReadyR, hArrow⟩ :=
    S.ramseyPass profiles κ Ready hReady hProfiles hBase hLift step
  let T := R.withBottomSystemGirth (hTerminalBottom R hReadyR)
  refine ⟨T, ?_, ?_⟩
  · exact hReadyR
  · exact hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
