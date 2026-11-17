import Girth.TrainCoverageFreePhysicalProjectedOrderPass
import Girth.TrainCoverageFreePhysicalProjectedRawFtStep
import Girth.TrainCoverageFreePhysicalProjectedRawFtWitness
import Girth.TrainCoverageFreePhysicalTrueActiveGirth
import Girth.TrainCoverageFreeInitialStage
import Girth.TrainRecursiveBottomEqualityBridge
import Girth.TrainRecursiveCompatibleOrderResult
import Girth.TrainRecursiveOrderRamseyBase
import Girth.TrainRecursiveOneEdgeDichotomy
import Girth.TrainPhysicalProjectedRankAssembly

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB : Type v}

/-- Convert the projected forest theorem to the unrestricted order witness
at the same vector by retaining a homomorphism to the large Ramsey base
on every reachable picture. -/
theorem unrestrictedPredicateOrder_of_projectedForest
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (B : RelStructure L.withOrder VB) [Finite VB] [LinearOrder VB]
    (hExtends : B.ExtendsOrder)
    (q : ℕ) (tail : List ℕ) (ht : Admissible (q :: tail))
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length)
    (symbols : Fin ((q :: tail).length + 1) → Set L.Symbol)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ x : VB, ∃ e : OldACarrierEdge A₀.ordered B, x ∈ e.1)
    (hGirth : GirthGT (supportCopies A₀.ordered B) q)
    (hParameters : targetTrain.AdjacentParameters (fun edge => edge.1)
      (allowedByPredicates B symbols))
    (hTargetCuts : ∀ j : Fin (q :: tail).length, 0 < j.val →
      LabelledGirthGT (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        ((q :: tail).get j))
    (hTargetTwo : ∃ a b : Embedding A₀.ordered B, ¬ SameCopy a b)
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (hForest : ProjectedFinePartiteForestAssertion A₀.ordered (q :: tail) κ) :
    UnrestrictedPredicateOrderWitness A₀.ordered B (q :: tail) targetTrain symbols κ := by
  classical
  have hHead : 2 ≤ q := ht.two_le q (by simp)
  have hTargetLinear : ALinear A₀.ordered B :=
    aLinear_of_girthGT_two A₀.ordered B (girthGT_mono hGirth hHead)
  obtain ⟨P, hFinite, D, family, hBaseLinear, hBaseStrong, hPullback, hBaseArrow⟩ :=
    exists_orderRamseyBase_of_extendsOrder A₀ B hExtends hTargetLinear κ symbols
  let : Finite P := hFinite
  let allowed := allowedByPredicates D symbols
  let : Nonempty family := by
    obtain ⟨b, hb, _⟩ := hBaseArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
    exact ⟨⟨b, hb⟩⟩
  have hBaseParameters (b : family) : targetTrain.AdjacentParameters
      (fun edge => edge.1) (fun ν => b.1 ⁻¹' allowed ν) := by
    simpa only [allowed, hPullback b.1 b.2] using hParameters
  have hCutoff (j : Fin (q :: tail).length) : 2 ≤ (q :: tail).get j :=
    ht.two_le _ (List.get_mem _ j)
  have hAllTargetCuts (j : Fin (q :: tail).length) :
      LabelledGirthGT (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        ((q :: tail).get j) := by
    by_cases hj : 0 < j.val
    · exact hTargetCuts j hj
    · have hJ : j = (⟨0, by simp⟩ : Fin (q :: tail).length) :=
        Fin.ext (Nat.eq_zero_of_not_pos hj)
      subst j
      exact targetTrain.bottom_labelledCutGirth_of_edgeGirth (fun edge => edge.1) q
        (physicalASupport_labelledGirth_of_girth A₀.ordered B q hGirth)
  let hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  let old := initialOrderStageReady_of_targetCuts A₀.ordered hA B D family q tail ht
    targetTrain allowed hSupportNonempty hSupportCovers hBaseParameters hCutoff hAllTargetCuts
  let S := PhysicalOrderStage.ofStrong hA old.1
  have hReady : S.toPhysicalForestStage.Ready := by
    constructor
    · simpa [S, PhysicalOrderStage.ofStrong, PhysicalForestStage.ofStrong,
        PhysicalForestStage.BottomReady, ForestStage.BottomReady] using old.2.1
    · exact old.2.2
  have hProject : S.system.toRelStructure.IsHomomorphism D S.system.part := old.1.isPartite.1
  obtain ⟨R, _, hSelectedArrow⟩ := PhysicalForestStage.ramseyOrder_of_projectingSteps
    A₀ S.toPhysicalForestStage κ hReady hProject hBaseArrow (by
      intro e T hCurrent hT hPair
      have hWagonGirth := PhysicalForestStage.trueActive_sameVectorCutGirth T e hCurrent.1
      obtain ⟨W, hW⟩ := PhysicalForestStage.rawPartiteFtWitness_of_projectedFinePartiteForestAssertion
        A₀ T e κ hT hPair hWagonGirth hForest
      exact RawPartiteFtWitness.toProjectedPictureStep A₀ T e κ W hT hW hBaseLinear hCurrent
        (fun b _ => hBaseStrong b.base b.base_mem) hTargetTwo hCutoff hPair)
  refine ⟨P, hFinite, D, family, ⟨{
    Vertex := R.Vertex
    finiteVertex := R.finiteVertex
    system := R.system
    projectsACopies := R.projectsACopies
    aLinear := R.aLinear
    supportNonempty := R.supportNonempty
    supportCovers := R.supportCovers
    selected := R.selected
    selectedPhysicalInjective := R.selectedPhysicalInjective
    strong := R.strong
    train := R.train
    targetRestriction := R.targetRestriction
    parameters := R.parameters
    allCutGirth := R.allCutGirth
    arrow := hSelectedArrow }⟩⟩

/-- The order assertion quantifies over the edge type, target, predicates
and finite palette independently at each vector. A shorter call may change
both the edge language and the palette. -/
def ProjectedOrderEverySpanningType (t : List ℕ) : Prop :=
  ∀ (L : RelLanguage.{u}) {UA : Type v}
    [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (A₀ : RelStructure L UA),
    (∃ (r : L.Symbol) (z : Fin (L.arity r) → UA), A₀.rel r z ∧ Function.Surjective z) →
    ∀ (κ : Type v) [Fintype κ] [Nonempty κ] {VB : Type v} [Finite VB] [LinearOrder VB]
      (B : RelStructure L.withOrder VB),
      B.ExtendsOrder →
      ∀ (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length)
        (symbols : Fin (t.length + 1) → Set L.Symbol),
        Nonempty (OldACarrierEdge A₀.ordered B) →
        (∀ x : VB, ∃ e : OldACarrierEdge A₀.ordered B, x ∈ e.1) →
        GirthGT (supportCopies A₀.ordered B) (t.headD 0) →
        targetTrain.AdjacentParameters (fun edge => edge.1) (allowedByPredicates B symbols) →
        (∀ j : Fin t.length, 0 < j.val →
          LabelledGirthGT (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
            (t.get j)) →
        UnrestrictedPredicateOrderWitness A₀.ordered B t targetTrain symbols κ

/-- The projected forest theorem gives the uniform unrestricted order
assertion at the same vector. A target with one edge uses the identity
Ramsey base. -/
theorem projectedOrderEverySpanningType_of_forest
    (t : List ℕ) (ht : Admissible t)
    (hForest : ProjectedForestEverySpanningType.{u, v} t) :
    ProjectedOrderEverySpanningType.{u, v} t := by
  intro L UA _ _ _ _ A₀ hSpan κ _ _ VB _ _ B hExtends targetTrain symbols
    hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts
  have hCases := two_copies_or_one_edge_order_stage A₀ B t ht targetTrain
    (allowedByPredicates B symbols) hSupportNonempty hSupportCovers κ
  rcases hCases with hTwo | ⟨S, hArrow⟩
  · cases t with
    | nil => exact False.elim (ht.nonempty rfl)
    | cons q tail =>
      exact unrestrictedPredicateOrder_of_projectedForest A₀ B hExtends q tail ht
        targetTrain symbols hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts
        hTwo κ (hForest L A₀ hSpan κ)
  · exact ⟨VB, inferInstance, B, {Embedding.id B},
      ⟨UnrestrictedOrderResult.ofOrderStage
        (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible S hArrow⟩⟩

/-- All rank operators except the cutoff-two step with nonempty tail
are supplied by the physical construction. -/
theorem projectedForestAndOrder_of_cutoffTwo
    (cutoffTwo : ∀ tail, Admissible tail → ProjectedOrderEverySpanningType.{u, v} tail →
      ProjectedForestEverySpanningType.{u, v} (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    ProjectedForestEverySpanningType.{u, v} t ∧ ProjectedOrderEverySpanningType.{u, v} t :=
  projectedForestAndOrder_of_cutoffTwo_and_conversion
    ProjectedOrderEverySpanningType cutoffTwo projectedOrderEverySpanningType_of_forest t ht

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
