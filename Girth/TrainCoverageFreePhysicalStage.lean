import Girth.TrainCoverageFreeACopyGeometry
import Girth.TrainCoverageFreeForestStage
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Correct physical stage invariant for forest-to-order conversion

The previous CoverageFree.ForestStage still stores full ordered
IsPartiteOver D. This is stronger than an arbitrary coloured-edge F_2
witness. Its own selected recursive development is conditional and
does not establish standalone F_t => R_t.

The physically sufficient replacement records only projections of
actual A-edges/copies to base A-copies. The physical A-support,
selected original B-labels, train restrictions, mixed finite forest,
all positive full-system bounds, and parameters are UNCHANGED.

The original stronger stage forgets to this one, but no converse is
claimed. Local attachment must be ported to the weaker stage before
the unconditional forest-to-order theorem can be validated.
Source only; no exact-head Lean compilation or axiom audit yet.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Standalone forest-stage interface with only correct physical
A-copy projection, not order-irreducible coverage. -/
structure PhysicalForestStage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    (family : Set (Embedding B D))
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : StructuralRamsey.Partite.System L P Vertex
  projectsACopies : ProjectsACopies A D system
  aLinear : ALinear A system.toRelStructure
  supportNonempty : Nonempty (OldACarrierEdge A system.toRelStructure)
  supportCovers : ∀ x : Vertex,
    ∃ edge : OldACarrierEdge A system.toRelStructure, x ∈ edge.1
  selected : Set (DesignatedCopy B D system family)
  selectedPhysicalInjective : Function.Injective
    (fun r : {b : DesignatedCopy B D system family // b ∈ selected} =>
      bSupportPiece A r.1.embedding)
  strong : ∀ b : DesignatedCopy B D system family,
    b ∈ selected →
      AStrong A system.toRelStructure (copyCarrier b.embedding)
  train : EdgeTrainLevels
    (OldACarrierEdge A system.toRelStructure) t.length
  targetRestriction : ∀ b : DesignatedCopy B D system family,
    b ∈ selected →
      ∀ μ : Fin (t.length + 1),
      ∀ a₁ a₂ : Embedding A B,
        train.rel μ (actualEdge (b.embedding.comp a₁))
          (actualEdge (b.embedding.comp a₂)) ↔
        targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)
  parameters : train.AdjacentParameters
    (fun edge => edge.1) (fun ν => system.part ⁻¹' allowed ν)
  bottomForest : FiniteMixedForestThrough
    (testedAB A B D system family selected) (t.headD 0)
  tailGirth : ∀ j : Fin t.length, 0 < j.val →
    (selectedPictureOrderOneData A B D system family selected
      train j.castSucc).FullSystemGirthGT (t.get j)

attribute [instance] PhysicalForestStage.finiteVertex

/-- Order stage additionally records full system girth at every
requested coordinate; it still needs no ambient mixedCoverage. -/
structure PhysicalOrderStage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    (family : Set (Embedding B D))
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    extends PhysicalForestStage A B D family t targetTrain allowed where
  allCutGirth : ∀ j : Fin t.length,
    (selectedPictureOrderOneData A B D system family selected
      train j.castSucc).FullSystemGirthGT (t.get j)

/-- The old coverage-free stage has more than the physical copy
projection we need, as soon as A is irreducible. -/
noncomputable def PhysicalForestStage.ofStrong
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (hA : A.Irreducible)
    (S : ForestStage A B D family t targetTrain allowed) :
    PhysicalForestStage A B D family t targetTrain allowed where
  Vertex := S.Vertex
  finiteVertex := S.finiteVertex
  system := S.system
  projectsACopies := projectsACopies_of_isPartiteOver
    A D S.system hA S.isPartite
  aLinear := S.aLinear
  supportNonempty := S.supportNonempty
  supportCovers := S.supportCovers
  selected := S.selected
  selectedPhysicalInjective := S.selectedPhysicalInjective
  strong := S.strong
  train := S.train
  targetRestriction := S.targetRestriction
  parameters := S.parameters
  bottomForest := S.bottomForest
  tailGirth := S.tailGirth

/-- A completed old order-stage likewise maps to the weaker
physical representation without changing any physical or selected
data. -/
noncomputable def PhysicalOrderStage.ofStrong
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (hA : A.Irreducible)
    (S : OrderStage A B D family t targetTrain allowed) :
    PhysicalOrderStage A B D family t targetTrain allowed where
  toPhysicalForestStage :=
    PhysicalForestStage.ofStrong hA S.toForestStage
  allCutGirth := S.allCutGirth

/-- Only base A-linearity and rigidity are needed to obtain the
strong gluing active carrier from a physical stage. -/
theorem PhysicalForestStage.activeCarrier_aStrong
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : PhysicalForestStage A B D family t targetTrain allowed)
    (hBaseLinear : ALinear A D)
    (e : Embedding A D)
    (hRigid : ∀ b : Embedding A D,
      SameCopy b e → b = e) :
    AStrong A S.system.toRelStructure
      (activeCarrier A S.system e.toFunctionEmbedding) :=
  activeCarrier_aStrong_of_projectedACopies
    A D S.system S.projectsACopies hBaseLinear e hRigid

/-- Forest-to-order promotion only adds the bottom full system
bound; all positive bounds were stored already. -/
noncomputable def PhysicalForestStage.withBottom
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (S : PhysicalForestStage A B D family (q :: tail)
      targetTrain allowed)
    (hBottom : (selectedPictureOrderOneData A B D
      S.system family S.selected S.train
      (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))).FullSystemGirthGT q) :
    PhysicalOrderStage A B D family (q :: tail) targetTrain allowed := by
  refine { toPhysicalForestStage := S, allCutGirth := ?_ }
  intro j
  by_cases hj : j.val = 0
  · have hJ : j = (⟨0, by simp⟩ : Fin (q :: tail).length) :=
      Fin.ext hj
    subst j
    simpa using hBottom
  · exact S.tailGirth j (by omega)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
