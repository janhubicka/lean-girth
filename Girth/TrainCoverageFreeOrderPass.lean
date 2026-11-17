import Girth.TrainCoverageFreeFinitePass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Coverage-free selected strong Ramsey pass at the SAME vector

The standalone circulation F_t assertion promises selected target
A-strongness, finite mixed forests, train/part parameters and
positive-cut system girth. It does NOT promise recursive-stage
mixed irreducible coverage.

The finite selected pass only needs these fields and two simple
readiness conditions:
(1) bottom system girth at the SAME q;
(2) every prescribed base B-embedding has a selected lift.

The second property holds in the actual disjoint initial picture
and is preserved by every selected transition. The first is
precisely the additional one-step bottom forest-to-order claim.

The entire finite selected Ramsey pass therefore yields a
coverage-free OrderStage and the ORIGINAL strong selected target
train Ramsey arrow without ever requesting mixed irreducible
coverage. The actual F_t local attachment must still be ported
to this weaker stage, so this theorem is conditional on legitimate
coverage-free picture steps, not an unconditional F_t=>R_t claim.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)}
variable {q : ℕ} {tail : List ℕ}
variable {targetTrain :
  EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
variable {allowed : Fin ((q :: tail).length + 1) → Set P}

/-- Exactly the two necessary readiness fields in the coverage-free
standalone finite pass; neither is a mixed irreducible-cover oracle. -/
def ForestStage.BottomReady
    (S : ForestStage A B D family (q :: tail) targetTrain allowed) : Prop :=
  (selectedPictureOrderOneData A B D S.system family S.selected
    S.train (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))).FullSystemGirthGT q

def ForestStage.CoversBase
    (S : ForestStage A B D family (q :: tail) targetTrain allowed) : Prop :=
  ∀ b : Embedding B D, b ∈ family →
    ∃ copy : DesignatedCopy B D S.system family,
      copy ∈ S.selected ∧ copy.base = b

def ForestStage.Ready
    (S : ForestStage A B D family (q :: tail) targetTrain allowed) : Prop :=
  S.BottomReady ∧ S.CoversBase

/-- Selected transition maps preserve every original prescribed
base B-copy's selected lift, with exactly the same base projection. -/
theorem TransitionEmbedding.coversBase
    {S T : ForestStage A B D family (q :: tail) targetTrain allowed}
    (f : TransitionEmbedding S T)
    (hCover : S.CoversBase) : T.CoversBase := by
  intro b hb
  obtain ⟨copy, hSelected, hBase⟩ := hCover b hb
  refine ⟨mapDesignated f.toPartite copy,
    f.map_selected copy hSelected, ?_⟩
  exact hBase

/-- A selected PictureStep transports the base lifts: pick one
constant colouring and retain its actual transition embedding. -/
theorem PictureStep.coversBase
    {S T : ForestStage A B D family (q :: tail) targetTrain allowed}
    {α : UA ↪ P} {κ : Type w} [Nonempty κ]
    (hStep : PictureStep S T α κ) (hBase : S.CoversBase) :
    T.CoversBase := by
  let constant :
      StructuralRamsey.Partite.ProjectedEmbedding A T.system α → κ :=
    fun _ => Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨f, _⟩ := hStep constant
  exact f.coversBase hBase

/-- The old picture's selected base-copy strongness extends to
every prescribed base B-copy by selected-lift coverage. This is
a transport fact and does not require mixed irreducible coverage
of any picture vertex. -/
theorem ForestStage.allBaseStrong_of_selected
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (hCovered : S.CoversBase)
    (hSelectedStrong : ∀ copy : DesignatedCopy B D S.system family,
      copy ∈ S.selected → AStrong A D (copyCarrier copy.base)) :
    ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b) := by
  intro b hb
  obtain ⟨copy, hSelected, hBase⟩ := hCovered b hb
  rw [← hBase]
  exact hSelectedStrong copy hSelected

/-- The SAME vector forest-to-order finite pass with no coverage
axiom beyond the actual selected B-base lifts. The local operator
must genuinely preserve bottom system girth and be a real selected
PictureStep, not merely an ordinary partite homogeneity claim. -/
theorem ForestStage.ramseyOrderPass_of_ready_steps
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.Ready)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBaseArrow : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family (q :: tail) targetTrain allowed),
      T.Ready →
        ∃ R : ForestStage A B D family (q :: tail)
          targetTrain allowed,
          R.BottomReady ∧ PictureStep T R α κ) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      DesignatedArrow R.toForestStage κ := by
  let Ready : List (UA ↪ P) →
      ForestStage A B D family (q :: tail) targetTrain allowed → Prop :=
    fun _ T => T.Ready
  have hStep : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family (q :: tail) targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestStage A B D family (q :: tail)
          targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ := by
    intro α remaining T hT
    obtain ⟨R, hBottom, hPicture⟩ := step α remaining T hT
    have hCover : R.CoversBase :=
      hPicture.coversBase hT.2
    exact ⟨R, ⟨hBottom, hCover⟩, hPicture⟩
  obtain ⟨T, hFinal, hArrow⟩ :=
    S.ramseyPass profiles κ Ready hInitial hProfiles
      hBaseArrow hInitial.2 hStep
  let R := T.withBottom hFinal.1
  exact ⟨R, hArrow⟩

/-- The returned selected Ramsey copy is A-strong and reflects
EVERY actual target train relation. It is still a genuine
coverage-free OrderStage, with no mixed irreducible-cover field. -/
theorem ForestStage.ramseyStrongTrain_of_ready_steps
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (hInitial : S.Ready)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBaseArrow : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestStage A B D family (q :: tail) targetTrain allowed),
      T.Ready →
        ∃ R : ForestStage A B D family (q :: tail)
          targetTrain allowed,
          R.BottomReady ∧ PictureStep T R α κ) :
    ∃ R : OrderStage A B D family (q :: tail) targetTrain allowed,
      ∀ χ : Embedding A R.system.toRelStructure → κ,
        ∃ b : DesignatedCopy B D R.system family,
          b ∈ R.selected ∧
          AStrong A R.system.toRelStructure (copyCarrier b.embedding) ∧
          (∀ μ : Fin ((q :: tail).length + 1),
            ∀ a₁ a₂ : Embedding A B,
              R.train.rel μ
                (actualEdge (b.embedding.comp a₁))
                (actualEdge (b.embedding.comp a₂)) ↔
              targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
          (∀ a₁ a₂ : Embedding A B,
            χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  obtain ⟨R, hArrow⟩ := S.ramseyOrderPass_of_ready_steps
    profiles κ hInitial hProfiles hBaseArrow step
  refine ⟨R, ?_⟩
  intro χ
  exact hArrow.strongTrain χ

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
