import Girth.ActualActiveDecorationBridge

/-!
# The true active subsystem's support is a covered transversal hypergraph

The structural local-forest theorem is applied not to an arbitrary
invented support system, but to the full A-support of the old true
active carrier. The latter automatically has two geometric properties:

1. Every active vertex lies in an induced A-copy, by the definition
   of the active carrier.
2. For finite ordered A, every actual A-copy contained in that
   active subsystem has precisely one vertex in each of its intrinsic
   A-part coordinates, by exact ordered projection.

Thus both vertex coverage and transversal support follow from the
actual old partite picture; they are not additional assumptions.
The old active-subsystem girth invariant supplies its high girth.
The remaining genuinely difficult input is the edge Ramsey
witness satisfying the bounded mixed-forest property.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- Every vertex of a true active carrier lies in a genuine induced
A-copy OF THAT ACTIVE SUBSYSTEM, not just of the old full picture. -/
theorem actualActiveSupport_vertexCovered
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (beta : UA ↪ P)
    (x : activeCarrier A C beta) :
    ∃ e : Set (activeCarrier A C beta),
      e ∈ supportCopies A
        (C.induce (activeCarrier A C beta)).toRelStructure ∧
      x ∈ e := by
  obtain ⟨a, u, hu⟩ := x.property
  let aS : StructuralRamsey.Partite.ProjectedEmbedding A
      (C.induce (activeCarrier A C beta)) beta :=
    activeInduceProjected A a (projected_mem_activeCarrier A C beta a)
  refine ⟨copyCarrier aS.val, ⟨aS.val, rfl⟩, ?_⟩
  exact ⟨u, Subtype.ext hu⟩

/-- Every edge of the actual ordered active A-support is transversal
to its actual A-valued part coordinates. -/
theorem actualActiveSupport_edgeTransversal
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (beta : RelStructure.Embedding A₀.ordered D) :
    EdgeTransversal
      (supportCopies A₀.ordered
        (C.induce (activeCarrier A₀.ordered C beta.toFunctionEmbedding)).toRelStructure)
      (activeSourcePart A₀.ordered C beta.toFunctionEmbedding) := by
  intro e he p
  obtain ⟨a, rfl⟩ := he
  refine ⟨a p, ⟨⟨p, rfl⟩, ?_⟩, ?_⟩
  · exact activeSourceACopy_part_identity A₀ D C hPartite beta a p
  · intro x hx
    obtain ⟨u, hu⟩ := hx.1
    have hUp : u = p := by
      calc
        u = activeSourcePart A₀.ordered C beta.toFunctionEmbedding (a u) :=
          (activeSourceACopy_part_identity A₀ D C hPartite beta a u).symm
        _ = activeSourcePart A₀.ordered C beta.toFunctionEmbedding x :=
          congrArg
            (activeSourcePart A₀.ordered C beta.toFunctionEmbedding) hu
        _ = p := hx.2
    calc
      x = a u := hu.symm
      _ = a p := congrArg a hUp

/-- Nonemptiness of the true active carrier implies that its actual
support hypergraph has at least one A-edge. -/
theorem actualActiveSupport_nonempty
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (beta : UA ↪ P)
    (hActive : (activeCarrier A C beta).Nonempty) :
    (supportCopies A
      (C.induce (activeCarrier A C beta)).toRelStructure).Nonempty := by
  obtain ⟨x, hx⟩ := hActive
  obtain ⟨e, he, _⟩ :=
    actualActiveSupport_vertexCovered A C beta ⟨x, hx⟩
  exact ⟨e, he⟩

end StructuralRamsey.Girth
