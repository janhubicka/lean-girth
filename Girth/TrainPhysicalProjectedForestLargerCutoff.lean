import Girth.TrainCoverageFreePhysicalLargerCutoff
import Girth.TrainCoverageFreePhysicalFineWitnessCoarsening
import Girth.TrainCoverageFreePhysicalFineRamseyBase

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA : Type v}

/-- At a head above two, construct the finite base, run the physical
refining pass and return its whole fine-partite forest witness. The only
recursive input is the lower assertion for each positive refinement depth. -/
theorem projectedFinePartiteForest_largerCutoff
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA] [Nontrivial UA]
    (hSpan : ∃ (r : L.Symbol) (z : Fin (L.arity r) → UA), A₀.rel r z ∧ Function.Surjective z)
    (q : ℕ) (tail : List ℕ) (ht : Admissible (q :: tail)) (hq : 2 < q)
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (hLower : ∀ d : ℕ, 0 < d → ProjectedFinePartiteForestAssertion A₀.ordered
      (List.replicate d (q - 1) ++ tail) κ) :
    ProjectedFinePartiteForestAssertion A₀.ordered (q :: tail) κ := by
  intro X _ Target targetTrain fineAllowed hTargetProject hFine hSupport hTwo hParameters hCuts
  let A := A₀.ordered
  have hGirth := ordinaryGirth_of_targetBottomLabelledCut A Target.toRelStructure targetTrain q
    (hCuts ⟨0, by simp⟩)
  obtain ⟨P, hFinite, D, family, hBaseFine, hBaseLinear, _hBaseCovers,
      hFamilyParts, hFamilyStrong, hBaseArrow, hBaseProject⟩ :=
    exists_projectingFinePartiteRamseyBase_of_spanningTuple A₀ Target hTargetProject
      hFine hSupport hTwo (girthGT_mono hGirth (by omega)) hSpan κ
  letI : Finite P := hFinite
  let allowed : Fin ((q :: tail).length + 1) → Set P := fun ν => D.part ⁻¹' fineAllowed ν
  have hOldAllowed (b : family) (ν : Fin ((q :: tail).length + 1)) :
      b.val ⁻¹' allowed ν = Target.part ⁻¹' fineAllowed ν := by
    ext x
    change D.part (b.val x) ∈ fineAllowed ν ↔ Target.part x ∈ fineAllowed ν
    rw [hFamilyParts b.val b.property x]
  have hBaseParameters (b : family) : targetTrain.AdjacentParameters (fun edge => edge.1)
      (fun ν => b.val ⁻¹' allowed ν) := by
    simpa only [hOldAllowed b] using hParameters
  have hSupportNonempty : Nonempty (OldACarrierEdge A Target.toRelStructure) := by
    obtain ⟨a, _, _⟩ := hTwo
    exact ⟨actualEdge a⟩
  have hSupportCovers (x : X) : ∃ e : OldACarrierEdge A Target.toRelStructure, x ∈ e.1 := by
    obtain ⟨a, hx⟩ := hSupport x
    exact ⟨actualEdge a, hx⟩
  obtain ⟨S, hProject, hArrow⟩ := ramseyForest_largerCutoff A₀
    (targetTrain := targetTrain) (allowed := allowed) ht hq hSupportNonempty
    hSupportCovers hBaseParameters hCuts hBaseLinear hFamilyStrong hTwo κ hBaseArrow hLower
  let W := PhysicalForestStage.toFinePartiteFtWitness Target D S fineAllowed
    (fun _ => rfl) hProject hBaseFine (fun b _ x => hFamilyParts b.base b.base_mem x) hArrow
  refine ⟨W, ?_⟩
  change S.system.toRelStructure.IsHomomorphism A (D.part ∘ S.system.part)
  intro r z hz
  exact hBaseProject r (S.system.part ∘ z) (hProject r z hz)

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
