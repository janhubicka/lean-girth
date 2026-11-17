import Girth.TrainRecursiveRefinementDoubleCount
import Girth.TrainRecursiveRefinementStepGirth
import Girth.CyclicRun

set_option autoImplicit false
set_option Elab.async false

/-!
# Track 6: non-singleton child fibres and one-step doubled localization

Each edge shares a child label with a cyclic neighbour. Counting the
occurrences bounds the number of used child labels and lets the
incidence-acyclicity argument localize the cycle inside one child.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E Child Part : Type v}

namespace LabelledBergeCycle

variable {edge : E → Set V} (C : LabelledBergeCycle edge)

/-- Each position of a Berge cycle has a cyclic neighbour in the same
child. Otherwise both boundary vertices of its edge lie in the permitted
part, contrary to edge transversality. -/
theorem adjacent_child_has_same_label_of_singleton_intersections
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (edge (C.label i)))
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (i : Fin C.length) :
    ∃ j : Fin C.length,
      (j = (finRotate C.length).symm i ∨ j = cyclicSucc i) ∧
        j ≠ i ∧ child j = child i := by
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
    exact hNone ⟨before, Or.inl rfl, hBeforeNe, h⟩
  have hNextDiff : child i ≠ child (cyclicSucc i) := by
    intro h
    exact hNone ⟨cyclicSucc i, Or.inr rfl, hNextNe, h.symm⟩
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
  obtain ⟨j, _, hj⟩ := C.adjacent_child_has_same_label_of_singleton_intersections
    child carrier part allowed hAllowed hEdgePart hContained hIntersection i
  exact ⟨j, hj⟩

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

/-- A family of transversal edges meeting only in one part is acyclic. -/
theorem labelledGirthGT_of_singleton_intersections
    (edge : E → Set V) (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ e, Set.InjOn part (edge e))
    (hIntersection : ∀ e f : E, e ≠ f →
      edge e ∩ edge f ⊆ part ⁻¹' allowed)
    (g : ℕ) : LabelledGirthGT edge g := by
  rintro ⟨C, _⟩
  let i : Fin C.length := ⟨0, by have := C.hlength; omega⟩
  obtain ⟨j, hne, hEq⟩ := C.child_has_second_occurrence_of_singleton_intersections
    C.label edge part allowed hAllowed (fun k => hEdgePart (C.label k))
    (fun _ => Set.Subset.rfl) hIntersection i
  exact hne (C.label_injective hEq)

namespace BergeCycle

/-- A physical Berge cycle is a labelled cycle with its actual edge
carriers as labels.  The doubled one-step localization therefore also
applies without an additional injectivity assumption on a synthetic
reindexing of edges.  This is the direct geometric statement used in
the manuscript. -/
theorem child_constant_of_singleton_intersections_twice
    {H : Set (Set V)} (C : BergeCycle H)
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (C.edge i))
    (hContained : ∀ i, C.edge i ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hLength : C.length ≤ 2 * g + 1) :
    ∀ i j : Fin C.length, child i = child j := by
  let labelled : LabelledBergeCycle (fun e : Set V => e) := {
    length := C.length
    hlength := C.hlength
    label := C.edge
    vertex := C.vertex
    label_injective := C.edge_injective
    vertex_injective := C.vertex_injective
    left_mem := C.left_mem
    right_mem := C.right_mem
  }
  exact labelled.child_constant_of_singleton_intersections_twice
    child carrier part allowed hAllowed hEdgePart hContained
    hIntersection g hg hGirth hLength

end BergeCycle
end StructuralRamsey.Girth

#print axioms StructuralRamsey.Girth.BergeCycle.child_constant_of_singleton_intersections_twice

#print axioms StructuralRamsey.Girth.LabelledBergeCycle.child_has_second_occurrence_of_singleton_intersections
#print axioms StructuralRamsey.Girth.LabelledBergeCycle.adjacent_child_has_same_label_of_singleton_intersections
#print axioms StructuralRamsey.Girth.LabelledBergeCycle.child_constant_of_singleton_intersections_twice
