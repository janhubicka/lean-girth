import Girth.TrainRecursiveWitnessPass
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Coverage-free forest-to-order picture stages

The standalone circulation assertion F_t does NOT promise that
irreducibles in its witness are covered by selected B-images or
ambient A-copies. The checked recursive ForestTailStage has an
extra mixedCoverage field that is useful for the recursive forest
lemma, but is stronger than F_t and is NOT required by R_t.

This module factors out the exact F_t/R_t stage data WITHOUT
mixedCoverage. All selected physical edge labels, train-cut
relations, actual strong selected B-copies, mixed finite forests,
part parameters, support and positive system bounds remain.

The forgetful map from a checked ForestTailStage is lossless on
all data except the explicitly forgotten coverage proof. The
reverse direction requires a real mixedCoverage certificate and
is not silently asserted. No new Ramsey or girth bound appears.

This is the FIRST structural step toward a standalone F_t -> R_t
conversion, not a completed replacement of the existing local
attachment constructor and Ramsey pass. The full coverage-free
picture-step construction remains an explicit obligation.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Exactly the forest/tail data used in the standalone F_t -> R_t
conversion, with NO selected mixed irreducible-cover premise. The
chosen selected B-family and ALL ambient A-edge labels are retained. -/
structure ForestStage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    (family : Set (Embedding B D))
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : StructuralRamsey.Partite.System L P Vertex
  isPartite : system.IsPartiteOver D
  aLinear : ALinear A system.toRelStructure
  supportNonempty : Nonempty (OldACarrierEdge A system.toRelStructure)
  supportCovers : ∀ x : Vertex,
    ∃ edge : OldACarrierEdge A system.toRelStructure, x ∈ edge.1
  selected : Set (DesignatedCopy B D system family)
  selectedPhysicalInjective : Function.Injective
    (fun q : {b : DesignatedCopy B D system family // b ∈ selected} =>
      bSupportPiece A q.1.embedding)
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

attribute [instance] ForestStage.finiteVertex

/-- The standalone R_t output adds only the requested full system
bounds. It still does NOT require mixed irreducible coverage. -/
structure OrderStage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    (family : Set (Embedding B D))
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    extends ForestStage A B D family t targetTrain allowed where
  allCutGirth : ∀ j : Fin t.length,
    (selectedPictureOrderOneData A B D system family selected
      train j.castSucc).FullSystemGirthGT (t.get j)

/-- A previously checked stronger stage is a genuine coverage-free
stage by forgetting ONLY its mixedCoverage proof. -/
noncomputable def ForestStage.ofStrong
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : TrainRecursiveWitness.ForestTailStage
      A B D family t targetTrain allowed) :
    ForestStage A B D family t targetTrain allowed where
  Vertex := S.Vertex
  finiteVertex := S.finiteVertex
  system := S.system
  isPartite := S.isPartite
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

/-- The same functor on already-completed order stages retains
every original cutoff certificate and all selected B-labels. -/
noncomputable def OrderStage.ofStrong
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : TrainRecursiveWitness.OrderStage
      A B D family t targetTrain allowed) :
    OrderStage A B D family t targetTrain allowed where
  toForestStage := ForestStage.ofStrong S.toForestTailStage
  allCutGirth := S.allCutGirth

/-- A coverage-free stage can be promoted to the checked recursive
stage only with a REAL mixed irreducible-coverage proof. This
explicitly records the missing direction of the comparison. -/
noncomputable def ForestStage.withMixedCoverage
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestStage A B D family t targetTrain allowed)
    (hCover : ∀ T : Set S.Vertex,
      (S.system.toRelStructure.induce T).Irreducible →
      (∃ b : DesignatedCopy B D S.system family,
        b ∈ S.selected ∧
        ∀ z : T, ∃ x : VB, z.1 = b.embedding x) ∨
      (∃ a : Embedding A S.system.toRelStructure,
        ∀ z : T, ∃ x : UA, z.1 = a x)) :
    TrainRecursiveWitness.ForestTailStage
      A B D family t targetTrain allowed where
  Vertex := S.Vertex
  finiteVertex := S.finiteVertex
  system := S.system
  isPartite := S.isPartite
  aLinear := S.aLinear
  supportNonempty := S.supportNonempty
  supportCovers := S.supportCovers
  selected := S.selected
  selectedPhysicalInjective := S.selectedPhysicalInjective
  mixedCoverage := hCover
  strong := S.strong
  train := S.train
  targetRestriction := S.targetRestriction
  parameters := S.parameters
  bottomForest := S.bottomForest
  tailGirth := S.tailGirth

/-- The only additional order-stage field missing from a forest
stage is bottom full system girth, since all positive cut bounds
are literally stored in its tailGirth field. No coverage proof
is introduced by this constructor. -/
noncomputable def ForestStage.withBottom
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (S : ForestStage A B D family (q :: tail) targetTrain allowed)
    (hBottom : (selectedPictureOrderOneData A B D
      S.system family S.selected S.train
      (⟨0, by simp⟩ : Fin ((q :: tail).length + 1))).FullSystemGirthGT q) :
    OrderStage A B D family (q :: tail) targetTrain allowed := by
  refine { toForestStage := S, allCutGirth := ?_ }
  intro j
  by_cases hj : j.val = 0
  · have hJ : j = (⟨0, by simp⟩ : Fin (q :: tail).length) :=
      Fin.ext hj
    subst j
    simpa using hBottom
  · exact S.tailGirth j (by omega)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
