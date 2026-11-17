import Girth.TrainPhysicalProjectedForestLargerCutoff
import Girth.TrainPhysicalPartiteForestBaseTwo

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v

/-- The recursive forest statement permits every finite edge type
with a spanning relation and all finite nonempty palettes. -/
def ProjectedForestEverySpanningType (t : List ℕ) : Prop :=
  ∀ (L : RelLanguage.{u}) {UA : Type v}
    [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (A₀ : RelStructure L UA)
    (hSpan : ∃ (r : L.Symbol) (z : Fin (L.arity r) → UA), A₀.rel r z ∧ Function.Surjective z)
    (κ : Type v) [Fintype κ] [Nonempty κ], ProjectedFinePartiteForestAssertion A₀.ordered t κ

/-- The actual cutoff-two base retains the tuple projection. -/
theorem projectedForestEverySpanningType_baseTwo : ProjectedForestEverySpanningType.{u, v} [2] := by
  intro L UA _ _ _ _ A₀ hSpan κ _ _ X _ Target sourceTrain allowed hTarget
    hFine hSupport hTwo hParameters hCut
  exact exists_projectingFinePartiteFtWitness_baseTwo_of_spanningTuple
    A₀ Target sourceTrain allowed hTarget hSpan hFine hSupport hTwo hParameters (hCut 0) κ

/-- Compose the actual base and larger-cutoff constructions with the two
remaining operators. The calls to the shorter assertion may change the
edge type and the finite palette. -/
theorem projectedForestAndOrder_of_cutoffTwo_and_conversion
    (OrderWitness : List ℕ → Prop)
    (cutoffTwo : ∀ tail, Admissible tail → OrderWitness tail →
      ProjectedForestEverySpanningType.{u, v} (2 :: tail))
    (forestToOrder : ∀ t, Admissible t → ProjectedForestEverySpanningType.{u, v} t →
      OrderWitness t)
    (t : List ℕ) (ht : Admissible t) :
    ProjectedForestEverySpanningType.{u, v} t ∧ OrderWitness t := by
  let ops : Operators ProjectedForestEverySpanningType.{u, v} OrderWitness := {
    baseTwo := projectedForestEverySpanningType_baseTwo
    forestToOrder := forestToOrder
    cutoffTwo := cutoffTwo
    largerCutoff := by
      intro q tail ht hq hLower L UA _ _ _ _ A₀ hSpan κ _ _
      exact projectedFinePartiteForest_largerCutoff A₀ hSpan q tail ht hq κ
        (fun d hd => (hLower d hd) L (UA := UA) A₀ hSpan κ) }
  have hForest := ops.assemble t ht
  exact ⟨hForest, forestToOrder t ht hForest⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
