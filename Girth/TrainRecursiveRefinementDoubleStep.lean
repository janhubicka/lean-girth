import Girth.TrainRecursiveRefinementDoubleCount
import Girth.TrainRecursiveRefinementStepGirth
import Girth.CyclicRun

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: non-singleton child fibres and one-step doubled localization

UNCHECKED CANDIDATE: no current local Lean toolchain; no manuscript
validation mark or proof certificate is claimed. Exact-head compilation,
`#print axioms`, and verification of the geometry inputs are required.

This builds on the existing checked `RawCyclicIncidenceData.compress`
and child-cut girth-to-incidence-acyclicity lemmas; no claim is made
about global retained cuts or existence of a recursive Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E Child Part : Type v}

namespace LabelledBergeCycle

variable {edge : E → Set V} (C : LabelledBergeCycle edge)

/-- A child label cannot appear exactly once in a physical Berge cycle:
the edge in that child would have both distinct boundary vertices in
the same permitted part, contradicting edge transversality. -/
theorem child_has_second_occurrence_of_singleton_intersections
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (edge (C.label i)))
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (i : Fin C.length) :
    ∃ j : Fin C.length, j ≠ i ∧ child j = child i := by
  classical
  let before : Fin C.length := (finRotate C.length).symm i
  have hBeforeSucc : cyclicSucc before = i := by
    simpa only [before, cyclicSucc_eq_finRotate] using
      (finRotate C.length).apply_symm_apply i
  have hNextNe : cyclicSucc i ≠ i :=
    RawCyclicIncidenceData.cyclicSucc_ne_self_of_two_le C.hlength i
  have hBeforeNe : before ≠ i := by
    intro heq
    apply hNextNe
    calc
      cyclicSucc i = cyclicSucc before := congrArg cyclicSucc heq.symm
      _ = i := hBeforeSucc
  by_contra hNone
  have hBeforeDiff : child before ≠ child i := by
    intro h
    exact hNone ⟨before, hBeforeNe, h⟩
  have hNextDiff : child i ≠ child (cyclicSucc i) := by
    intro h
    exact hNone ⟨cyclicSucc i, hNextNe, h.symm⟩
  have hBeforeIn : C.vertex before ∈ edge (C.label i) := by
    simpa only [hBeforeSucc] using C.right_mem before
  have hPermBefore : part (C.vertex before) ∈ allowed :=
    hIntersection (child before) (child i) hBeforeDiff
      ⟨hContained before (C.left_mem before), hContained i hBeforeIn⟩
  have hPermAfter : part (C.vertex i) ∈ allowed :=
    hIntersection (child i) (child (cyclicSucc i)) hNextDiff
      ⟨hContained i (C.left_mem i),
       hContained (cyclicSucc i) (C.right_mem i)⟩
  have hVerticesEq : C.vertex before = C.vertex i :=
    hEdgePart i hBeforeIn (C.left_mem i) (hAllowed hPermBefore hPermAfter)
  exact hBeforeNe (C.vertex_injective hVerticesEq)

/-- If a physical cycle has at most `2*g+1` edges, the used child
set has at most `g` elements. A nonconstant child word would then
give a cyclic incidence walk in an acyclic labelled child family. -/
theorem child_constant_of_singleton_intersections_twice
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (edge (C.label i)))
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hLength : C.length ≤ 2 * g + 1) :
    ∀ i j : Fin C.length, child i = child j := by
  classical
  let Used : Type v := Set.range child
  let picked : Fin C.length → Used := fun i => ⟨child i, ⟨i, rfl⟩⟩
  have hOnto : Function.Surjective picked := by
    rintro ⟨p, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext hi⟩
  haveI : Finite Used := Finite.of_surjective picked hOnto
  letI : Fintype Used := Fintype.ofFinite Used
  have hTwo : ∀ u : Used, ∃ p : Fin C.length × Fin C.length,
      p.1 ≠ p.2 ∧ picked p.1 = u ∧ picked p.2 = u := by
    rintro ⟨u, ⟨i, hi⟩⟩
    obtain ⟨j, hji, hj⟩ := C.child_has_second_occurrence_of_singleton_intersections
      child carrier part allowed hAllowed hEdgePart hContained hIntersection i
    exact ⟨(i, j), hji.symm, Subtype.ext hi, Subtype.ext (hj.trans hi)⟩
  have hCard : Fintype.card Used ≤ g := by
    have hTwice := card_double_le_of_two_preimages picked hTwo
    omega
  let usedCarrier : Used → Set V := fun p => carrier p.val
  have hUsedGirth : LabelledGirthGT usedCarrier g :=
    labelledGirthGT_of_injective_reindex carrier Subtype.val
      Subtype.val_injective g hGirth
  have hAcyclic : (boundaryIncidenceGraph usedCarrier).IsAcyclic :=
    labelledGirthGT_incidence_acyclic_of_card usedCarrier g hg hCard hUsedGirth
  by_contra hNonconstant
  push Not at hNonconstant
  obtain ⟨i, j, hij⟩ := hNonconstant
  let raw : RawCyclicIncidenceData usedCarrier := {
    length := C.length
    hlength := C.hlength
    label := picked
    connector := C.vertex
    connector_injective := C.vertex_injective
    boundary_mem := fun k _ =>
      ⟨hContained k (C.left_mem k),
        hContained (cyclicSucc k) (C.right_mem k)⟩
    nonconstant := ⟨i, j, fun h => hij (congrArg Subtype.val h)⟩
  }
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic hAcyclic raw.compress

end LabelledBergeCycle
end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.LabelledBergeCycle.child_has_second_occurrence_of_singleton_intersections
#print axioms StructuralRamsey.Girth.LabelledBergeCycle.child_constant_of_singleton_intersections_twice
