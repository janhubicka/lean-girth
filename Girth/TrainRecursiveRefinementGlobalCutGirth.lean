import Girth.TrainRecursiveRefinementGirthGain
import Girth.TrainRecursiveInitialTailIncidence

set_option autoImplicit false

/-!
# Global girth gain from a retained first-wagon cut

The existing refinement girth gain is local to one original first wagon.
To globalize it in the nonempty-tail case, first use the ORIGINAL retained
first-wagon labelled cut at the desired cutoff.  A short physical labelled
edge cycle cannot change its first-wagon class: restricting the complete
labelled wagon family to the finitely many classes actually visited gives
an acyclic incidence graph, while every class transition contributes a
genuine vertex connector to a cyclic incidence walk.

Crucially, labels are quotient classes of physical edges, *not* their
vertex-carrier sets.  Distinct classes are not collapsed if carriers agree,
and the original physical edge family is not pruned.  The geometric
first-refinement parameters and child girth are already packaged by
FirstWagonRefinement, which then excludes cycles inside one first wagon.
This settles the finite global girth-gain interface conditional on the
true retained first-cut bound, not existence of the recursive witness.
-/

namespace StructuralRamsey.Girth

universe u v

section RetainedCutLocalization

variable {E W : Type v}

/-- A short labelled physical-edge cycle is contained in one genuine
quotient wagon class whenever the COMPLETE labelled wagon cut has the
corresponding girth bound.  This uses no injectivity of physical edge
carriers, nor any spurious total-finiteness hypothesis. -/
theorem EdgeTrainLevels.labelledCycle_rel_constant_of_cutGirth
    {m : ℕ} (T : EdgeTrainLevels E m)
    (edge : E → Set W) (μ : Fin (m + 1))
    (q : ℕ) (hq : 2 ≤ q)
    (hCut : LabelledGirthGT (T.wagonClassCarrier edge μ) q)
    (C : LabelledBergeCycle edge) (hLength : C.length ≤ q) :
    ∀ i j : Fin C.length, T.rel μ (C.label i) (C.label j) := by
  classical
  let owner : Fin C.length → Quotient (T.wagonSetoid μ) :=
    fun i => Quotient.mk (T.wagonSetoid μ) (C.label i)
  have hConstant : ∀ i j : Fin C.length, owner i = owner j := by
    by_contra hNot
    push_neg at hNot
    obtain ⟨i, j, hij⟩ := hNot
    let Used : Type v := Set.range owner
    let picked : Fin C.length → Used :=
      fun k => ⟨owner k, ⟨k, rfl⟩⟩
    have hOnto : Function.Surjective picked := by
      rintro ⟨p, ⟨k, hk⟩⟩
      exact ⟨k, Subtype.ext hk⟩
    haveI : Finite Used := Finite.of_surjective picked hOnto
    letI : Fintype Used := Fintype.ofFinite Used
    have hCard : Fintype.card Used ≤ q := by
      have hc : Fintype.card Used ≤ Fintype.card (Fin C.length) :=
        Fintype.card_le_of_surjective picked hOnto
      have hc' : Fintype.card Used ≤ C.length := by simpa using hc
      omega
    let carrier : Used → Set W :=
      fun p => T.wagonClassCarrier edge μ p.val
    have hUsedGirth : LabelledGirthGT carrier q :=
      labelledGirthGT_of_injective_reindex
        (T.wagonClassCarrier edge μ)
        Subtype.val Subtype.val_injective q hCut
    have hAcyclic : (boundaryIncidenceGraph carrier).IsAcyclic :=
      labelledGirthGT_incidence_acyclic_of_card
        carrier q hq hCard hUsedGirth
    have hBoundary : ∀ k, picked k ≠ picked (cyclicSucc k) →
        C.vertex k ∈ carrier (picked k) ∧
        C.vertex k ∈ carrier (picked (cyclicSucc k)) := by
      intro k _
      constructor
      · change C.vertex k ∈ T.wagonCarrier edge μ (C.label k)
        exact ⟨C.label k, (T.equivalent μ).refl _, C.left_mem k⟩
      · change C.vertex k ∈ T.wagonCarrier edge μ (C.label (cyclicSucc k))
        exact ⟨C.label (cyclicSucc k),
          (T.equivalent μ).refl _, C.right_mem k⟩
    let raw : RawCyclicIncidenceData carrier := {
      length := C.length
      hlength := C.hlength
      label := picked
      connector := C.vertex
      connector_injective := C.vertex_injective
      boundary_mem := hBoundary
      nonconstant := ⟨i, j, fun h => hij (congrArg Subtype.val h)⟩
    }
    exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic
      hAcyclic raw.compress
  intro i j
  exact Quotient.exact (hConstant i j)

end RetainedCutLocalization

section GlobalRefinement

variable {E W P : Type v}
variable {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
variable {edge : E → Set W} {part : W → P} {firstAllowed : Set P} {g : ℕ}

/-- A first-wagon refinement PLUS labelled girth of the actual retained
first wagon cut rules out every short physical edge cycle, even those
crossing several original first wagons.  The refinement itself supplies
the within-wagon contradiction; the retained cut supplies localization. -/
theorem FirstWagonRefinement.labelledGirthGT_of_retainedFirstCut
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g)
    (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (hFirstCut : LabelledGirthGT
      (T.wagonClassCarrier edge (⟨1, by omega⟩ : Fin (m + 1))) (g + 1)) :
    LabelledGirthGT edge (g + 1) := by
  rintro ⟨C, hLength⟩
  have hFirst : ∀ i j : Fin C.length,
      T.rel ⟨1, by omega⟩ (C.label i) (C.label j) :=
    T.labelledCycle_rel_constant_of_cutGirth
      edge ⟨1, by omega⟩ (g + 1) (by omega)
      hFirstCut C hLength
  exact R.false_of_short_labelledCycle_in_firstWagon
    hg hEdgePart C hLength hFirst

/-- The unlabelled physical-edge girth statement follows as a corollary,
without needing the original first cut to be universal. -/
theorem FirstWagonRefinement.girthGT_of_retainedFirstCut
    (R : FirstWagonRefinement T hm edge part firstAllowed g)
    (hg : 2 ≤ g)
    (hEdgePart : ∀ e : E, Set.InjOn part (edge e))
    (hFirstCut : LabelledGirthGT
      (T.wagonClassCarrier edge (⟨1, by omega⟩ : Fin (m + 1))) (g + 1)) :
    GirthGT (Set.range edge) (g + 1) :=
  (R.labelledGirthGT_of_retainedFirstCut hg hEdgePart hFirstCut).range_girth

end GlobalRefinement

section ActualGlobal

variable {L : RelLanguage.{u}} {UA X P : Type v}

/-- Complete ordinary A-support girth >g+1 in a genuine partite system
from the physical refinement and the OLD retained first-cut labelled
girth >g+1.  Irreducibility supplies the edge part-transversality. -/
theorem FirstWagonRefinement.actualSupport_girthGT_of_retainedFirstCut
    (A : RelStructure L UA) (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    {m : ℕ} {T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m}
    {hm : 0 < m} {allowed : Set P} {g : ℕ}
    (R : FirstWagonRefinement T hm (fun e => e.val) C.part allowed g)
    (hg : 2 ≤ g)
    (hFirstCut : LabelledGirthGT
      (T.wagonClassCarrier (fun e => e.val)
        (⟨1, by omega⟩ : Fin (m + 1))) (g + 1)) :
    GirthGT (supportCopies A C.toRelStructure) (g + 1) := by
  have h := R.girthGT_of_retainedFirstCut
    hg (actualASupport_part_injOn A hA C) hFirstCut
  apply girthGT_of_subset ?_ h
  intro s hs
  exact ⟨⟨s, hs⟩, rfl⟩

end ActualGlobal

end StructuralRamsey.Girth
