import Girth.TrainCoverageFreeFinitePass
import Girth.TrainRecursiveLargeBaseCoarsening
import Girth.TrainRecursiveCoarsenedSelectedFamilyArrow
import Girth.TrainIndexedPartitePhysicalArrow
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The standalone F_t local lower witness after genuine large-base coarsening

This ports ONLY those consequences of a lower selected forest witness
which do not depend on recursive mixed irreducible coverage.

A local F_t witness lives over a LARGE A-partite base: the full
nontrivial target has repeated A-parts and cannot project injectively
to the small A-base. Coarsen the witness's part map through the large
base and keep each selected copy indexed by its literal selected label.
No physical edge or wagon label changes.

The result supplies A-partiteness, injective COMPLETE support pieces,
finite mixed SET forest through q, exact all-cut selected train
restriction, adjacent parameters and the INDEXED PHYSICAL edge arrow.
No assertion IrreduciblesExtendTo is needed, proved or assumed.

This source has NOT been compiled at an exact Lean head. It does not
establish existence of the F_t witness or the final attachment step.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P I : Type v}

section ForestSubfamily

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (S : ForestStage A B D family t targetTrain allowed)

/-- The selected subfamily inherits the exact mixed finite-SET forest
from F_t. It need not cover the ambient structure. -/
theorem ForestStage.selectedEmbeddings_mixedForest
    (f : I → Embedding B S.system.toRelStructure)
    (hSelected : ∀ i, ∃ b : DesignatedCopy B D S.system family,
      b ∈ S.selected ∧ f i = b.embedding)
    (q : ℕ) (hq : q ≤ t.headD 0) :
    FiniteMixedForestThrough (RelationalMixedSupportTest A f) q := by
  intro s hTest hCard
  apply S.bottomForest s ?_ (hCard.trans hq)
  intro piece hp
  rcases hTest piece hp with ⟨i, hi⟩ | ⟨a, ha⟩
  · obtain ⟨b, hb, hfi⟩ := hSelected i
    exact Or.inr ⟨b, hb, by simpa only [hfi] using hi⟩
  · exact Or.inl ⟨a, ha⟩

end ForestSubfamily

section SelectedLowerBundle

variable (A₀ : RelStructure L UA)
variable [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
variable (Target : StructuralRamsey.Partite.System L.withOrder UA VB)
variable (Large : StructuralRamsey.Partite.System L.withOrder UA P)
variable {family : Set (Embedding Target.toRelStructure Large.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A Target.toRelStructure) t.length}
variable (fineAllowed : Fin (t.length + 1) → Set UA)
variable (S : ForestStage A Target.toRelStructure Large.toRelStructure
  family t targetTrain (fun ν => Large.part ⁻¹' fineAllowed ν))

/-- All coverage-free local F_t data required by the physical attachment,
EXCEPT the positive FULL gluing bounds (handled separately) and the
A-to-processed-base relabelling. One selected family index is retained. -/
theorem ForestStage.coarsenedSelected_Ft_noCoverage_bundle
    (hTarget : Target.IsPartiteOver A)
    (hLarge : Large.IsPartiteOver A)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      Large.part (b x) = Target.part x)
    (q : ℕ) (hq : q ≤ t.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow S κ) :
    let E := S.system.coarsenVia Large S.isPartite
    let J := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure S.system family // b ∈ S.selected}
    let f : J → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target Large S.system S.isPartite family hFamilyParts
        S.selected i
    E.IsPartiteOver A ∧
    Function.Injective
      (fun i : J => bSupportPiece A ((f i).toEmbedding)) ∧
    FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun i : J => (f i).toEmbedding)) q ∧
    (∀ ν : Fin (t.length + 1), ∀ i : J,
      ∀ a b : Embedding A Target.toRelStructure,
        S.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        targetTrain.rel ν (actualEdge a) (actualEdge b)) ∧
    S.train.AdjacentParameters (fun edge => edge.1)
      (fun ν => E.part ⁻¹' fineAllowed ν) ∧
    (∀ χ : OldACarrierEdge A E.toRelStructure → κ,
      ∃ i : J, ∀ a b : Embedding A Target.toRelStructure,
        χ (actualEdge ((f i).toEmbedding.comp a)) =
          χ (actualEdge ((f i).toEmbedding.comp b))) := by
  let E := S.system.coarsenVia Large S.isPartite
  let J := {b : DesignatedCopy Target.toRelStructure
    Large.toRelStructure S.system family // b ∈ S.selected}
  let f : J → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target Large S.system S.isPartite family hFamilyParts
      S.selected i
  have hPartite : E.IsPartiteOver A :=
    StructuralRamsey.Partite.System.coarsenVia_isPartiteOver
      Large S.system A S.isPartite hLarge
  have hInjective :
      Function.Injective
        (fun i : J => bSupportPiece A ((f i).toEmbedding)) := by
    change Function.Injective
      (fun i : J => bSupportPiece A i.1.embedding)
    exact S.selectedPhysicalInjective
  have hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun i : J => (f i).toEmbedding)) q := by
    apply S.selectedEmbeddings_mixedForest
      (fun i : J => (f i).toEmbedding) ?_ q hq
    intro i
    exact ⟨i.1, i.2, rfl⟩
  have hRestriction : ∀ ν : Fin (t.length + 1), ∀ i : J,
      ∀ a b : Embedding A Target.toRelStructure,
        S.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        targetTrain.rel ν (actualEdge a) (actualEdge b) := by
    intro ν i a b
    change S.train.rel ν
      (actualEdge (i.1.embedding.comp a))
      (actualEdge (i.1.embedding.comp b)) ↔
      targetTrain.rel ν (actualEdge a) (actualEdge b)
    exact S.targetRestriction i.1 i.2 ν a b
  have hParameters : S.train.AdjacentParameters
      (fun edge => edge.1)
      (fun ν => E.part ⁻¹' fineAllowed ν) := by
    change S.train.AdjacentParameters (fun edge => edge.1)
      (fun ν => S.system.part ⁻¹' (Large.part ⁻¹' fineAllowed ν))
    exact S.parameters
  have hIndexed :=
    selectedPartiteFamilyArrow_after_coarsen_of_designatedRelationalArrow
      A Target Large S.system S.isPartite family hFamilyParts
      S.selected κ (by
        intro χ
        obtain ⟨b, hb, hMono⟩ := hArrow χ
        exact ⟨⟨b, hb⟩, hMono⟩)
  have hPhysical :=
    indexedPhysicalArrow_of_partiteFamilyArrow_for_orderedA
      A₀ Target E f hTarget κ hIndexed
  exact ⟨hPartite, hInjective, hForest,
    hRestriction, hParameters, hPhysical⟩

end SelectedLowerBundle

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree
