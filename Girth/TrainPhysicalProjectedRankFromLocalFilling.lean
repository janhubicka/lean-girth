import Girth.TrainPhysicalProjectedForestCutoffTwo
import Girth.TrainRecursiveProjectedOrderConversion

set_option autoImplicit false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v

/-- The remaining generator constructs a raw local filling from the
strictly shorter unrestricted order theorem. -/
def CutoffTwoLocalFillingFromShorterOrder : Prop :=
  ∀ tail, Admissible tail → ProjectedOrderEverySpanningType.{u, v} tail →
    ∀ (L : RelLanguage.{u}) {UA : Type v}
      [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
      (A₀ : RelStructure L UA),
      (∃ (r : L.Symbol) (z : Fin (L.arity r) → UA),
        A₀.rel r z ∧ Function.Surjective z) →
      ∀ (κ : Type v) [Fintype κ] [Nonempty κ],
        ProjectedCutoffTwoLocalAssertion A₀.ordered tail κ

/-- Assemble the full well-founded recursion from the raw cutoff-two
filling. The forest and order passes, including both initial pictures,
are constructed by the verified physical proofs. -/
theorem projectedForestAndOrder_of_localFilling
    (fill : CutoffTwoLocalFillingFromShorterOrder.{u, v})
    (t : List ℕ) (ht : Admissible t) :
    ProjectedForestEverySpanningType.{u, v} t ∧ ProjectedOrderEverySpanningType.{u, v} t := by
  apply projectedForestAndOrder_of_cutoffTwo _ t ht
  intro tail hTail hOrder L UA _ _ _ _ A₀ hSpan κ _ _
  have hTwo : Admissible (2 :: tail) := by
    refine ⟨by simp, List.pairwise_cons.mpr ⟨hTail.two_le, hTail.nondecreasing⟩, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact le_rfl
    · exact hTail.two_le q hq
  have hLocal : ProjectedCutoffTwoLocalAssertion A₀.ordered tail κ :=
    @fill tail hTail hOrder L UA _ _ _ _ A₀ hSpan κ _ _
  exact @projectedFinePartiteForest_cutoffTwo L UA A₀ _ _ _ _ hSpan tail hTwo κ _ _ hLocal

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
