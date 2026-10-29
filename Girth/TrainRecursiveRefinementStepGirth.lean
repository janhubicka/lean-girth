import Girth.TrainRecursiveInitialTailIncidence

/-!
# One refinement step localizes cycles through the next cutoff

Consider the complete labelled family of children of one fixed parent.
Different children meet only in one permitted part, and the part map is
injective on every actual source edge.  A genuine edge cycle cannot use a
different child at every position: the two distinct boundary vertices of
an occurrence would then lie in the same part of that edge.

Consequently a cycle of length at most `g + 1` uses at most `g` child labels.
Labelled child girth greater than `g` makes that finite incidence graph
acyclic.  The existing cyclic-run compression then forces the child word
to be constant.  This is the one-level geometric gain, with no assumed
ordinary output girth and no removal of ambient edges.

The train application instantiates `Child` with the subtype of all children
of the chosen parent.  This theorem makes no claim about cycles spanning
different parents until an appropriate higher-cut bound is supplied.
-/

namespace StructuralRamsey.Girth

universe v
variable {V E Child Part : Type v}

namespace LabelledBergeCycle

variable {edge : E → Set V} (C : LabelledBergeCycle edge)

/-- Singleton sibling intersections and actual edge transversality force
some repetition in the child word of every genuine edge cycle. -/
theorem child_not_injective_of_singleton_intersections
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (edge (C.label i)))
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed) :
    ¬ Function.Injective child := by
  intro hInjective
  let i : Fin C.length := ⟨0, by have := C.hlength; omega⟩
  let j : Fin C.length := cyclicSucc i
  have hij : i ≠ j :=
    (RawCyclicIncidenceData.cyclicSucc_ne_self_of_two_le C.hlength i).symm
  have hjs : j ≠ cyclicSucc j :=
    (RawCyclicIncidenceData.cyclicSucc_ne_self_of_two_le C.hlength j).symm
  have hChildIJ : child i ≠ child j := fun h => hij (hInjective h)
  have hChildJS : child j ≠ child (cyclicSucc j) := fun h => hjs (hInjective h)
  have hx : part (C.vertex i) ∈ allowed :=
    hIntersection (child i) (child j) hChildIJ
      ⟨hContained i (C.left_mem i), hContained j (C.right_mem i)⟩
  have hy : part (C.vertex j) ∈ allowed :=
    hIntersection (child j) (child (cyclicSucc j)) hChildJS
      ⟨hContained j (C.left_mem j), hContained (cyclicSucc j) (C.right_mem j)⟩
  have hxy : C.vertex i = C.vertex j :=
    hEdgePart j (C.right_mem i) (C.left_mem j) (hAllowed hx hy)
  exact hij (C.vertex_injective hxy)

/-- A cycle through cutoff `g + 1` stays in one child when that parent's
full labelled child family has girth greater than `g` and singleton-part
sibling intersections.  Only the actually occurring edge carriers need
the part-transversality assumption.
-/
theorem child_constant_of_singleton_intersections
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (edge (C.label i)))
    (hContained : ∀ i, edge (C.label i) ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hLength : C.length ≤ g + 1) :
    ∀ i j : Fin C.length, child i = child j := by
  classical
  have hNotInjective := C.child_not_injective_of_singleton_intersections
    child carrier part allowed hAllowed hEdgePart hContained hIntersection
  let Used : Type v := Set.range child
  let picked : Fin C.length → Used := fun i => ⟨child i, ⟨i, rfl⟩⟩
  have hOnto : Function.Surjective picked := by
    rintro ⟨p, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext hi⟩
  haveI : Finite Used := Finite.of_surjective picked hOnto
  letI : Fintype Used := Fintype.ofFinite Used
  have hPickedNotInjective : ¬ Function.Injective picked := by
    intro h
    apply hNotInjective
    intro i j hij
    exact h (Subtype.ext hij)
  have hCardLt : Fintype.card Used < C.length := by
    simpa only [Fintype.card_fin] using
      Fintype.card_lt_of_surjective_not_injective picked hOnto hPickedNotInjective
  have hCard : Fintype.card Used ≤ g := by omega
  let usedCarrier : Used → Set V := fun p => carrier p.val
  have hUsedGirth : LabelledGirthGT usedCarrier g :=
    labelledGirthGT_of_injective_reindex carrier Subtype.val Subtype.val_injective g hGirth
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
      ⟨hContained k (C.left_mem k), hContained (cyclicSucc k) (C.right_mem k)⟩
    nonconstant := ⟨i, j, fun h => hij (congrArg Subtype.val h)⟩
  }
  exact CyclicIncidenceData.no_cyclicIncidenceData_of_acyclic hAcyclic raw.compress

end LabelledBergeCycle

namespace BergeCycle

/-- Physical Berge cycles satisfy the same one-level refinement
localization.  Their physical edges supply the literal edge labels. -/
theorem child_constant_of_singleton_intersections
    {H : Set (Set V)} (C : BergeCycle H)
    (child : Fin C.length → Child) (carrier : Child → Set V)
    (part : V → Part) (allowed : Set Part)
    (hAllowed : allowed.Subsingleton)
    (hEdgePart : ∀ i, Set.InjOn part (C.edge i))
    (hContained : ∀ i, C.edge i ⊆ carrier (child i))
    (hIntersection : ∀ a b : Child, a ≠ b →
      (carrier a ∩ carrier b) ⊆ part ⁻¹' allowed)
    (g : ℕ) (hg : 2 ≤ g) (hGirth : LabelledGirthGT carrier g)
    (hLength : C.length ≤ g + 1) :
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
  exact labelled.child_constant_of_singleton_intersections child carrier part allowed
    hAllowed hEdgePart hContained hIntersection g hg hGirth hLength

end BergeCycle
end StructuralRamsey.Girth
