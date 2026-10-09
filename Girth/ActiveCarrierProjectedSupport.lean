import Girth.UntouchedProjectedGirth
import Girth.ActiveCarrierStrong

/-!
# A-copies inside an ordered active carrier project to its base copy

The active carrier for a base A-copy consists of the vertices occurring
in A-copies projected to that base embedding. An arbitrary additional
A-copy lying wholly INSIDE this carrier also projects to that base copy:
the partite base factorization has its whole image inside the fixed
base A-carrier, so finiteness makes the base copies equal; the source
linear order makes the base embedding unique.

Unlike the strongness of the active carrier (which controls A-copies
meeting it in two vertices), this contained-copy statement requires
no ambient A-linearity. It is the missing exact-projection interface
between the actual induced active subsystem and the projected edge
family used by the untouched-subsystem girth argument.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- Every ambient A-copy carried entirely by the induced active
subsystem projects EXACTLY to the prescribed ordered base embedding.
No ambient A-linearity is needed for this contained-copy statement. -/
theorem activeInduced_ACopy_projects_ordered
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (β : RelStructure.Embedding A₀.ordered D)
    (a : RelStructure.Embedding A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure) :
    ∃ proj : StructuralRamsey.Partite.ProjectedEmbedding
        A₀.ordered C β.toFunctionEmbedding,
      ∀ u : UA,
        proj.val u =
          ((StructuralRamsey.Partite.System.inclusion C
            (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding.comp a) u := by
  classical
  let S := activeCarrier A₀.ordered C β.toFunctionEmbedding
  let inc : RelStructure.Embedding
      (C.induce S).toRelStructure C.toRelStructure :=
    (StructuralRamsey.Partite.System.inclusion C S).toEmbedding
  let aWhole : RelStructure.Embedding A₀.ordered C.toRelStructure :=
    inc.comp a
  obtain ⟨b, hb⟩ :=
    hPartite.after_irreducible_embedding
      (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible aWhole
  have hBaseRange (u : UA) : ∃ v : UA, b u = β v := by
    obtain ⟨e, ⟨v, hv⟩⟩ := (a u).property
    refine ⟨v, ?_⟩
    calc
      b u = C.part (aWhole u) := hb u
      _ = C.part (e.val v) := congrArg C.part hv.symm
      _ = β v := e.property v
  have hSame : SameCopy b β :=
    sameCopy_of_range_subset b β hBaseRange
  have hbEq : b = β :=
    ordered_embedding_eq_of_sameCopy b β hSame
  let proj : StructuralRamsey.Partite.ProjectedEmbedding
      A₀.ordered C β.toFunctionEmbedding := {
    val := aWhole
    property := by
      intro u
      have h := hb u
      rw [hbEq] at h
      exact h.symm
  }
  exact ⟨proj, by intro u; rfl⟩

/-- Every support edge of the actual induced active carrier, mapped
into the full picture, is a genuine beta-projected support edge.
This identifies the direction needed to transfer the projected
girth theorem to the induced active subsystem. -/
theorem mapped_activeSupport_subset_projected_ordered
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (D : RelStructure L.withOrder P)
    (C : StructuralRamsey.Partite.System L.withOrder P X)
    (hPartite : C.IsPartiteOver D)
    (β : RelStructure.Embedding A₀.ordered D) :
    mappedSupportCopies A₀.ordered
      (C.induce
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toRelStructure
      C.toRelStructure
      (StructuralRamsey.Partite.System.inclusion C
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding
      ⊆ projectedSupportCopies A₀.ordered C β.toFunctionEmbedding := by
  intro T hT
  obtain ⟨a, hEq⟩ := hT
  obtain ⟨proj, hProj⟩ :=
    activeInduced_ACopy_projects_ordered A₀ D C hPartite β a
  refine ⟨proj, ?_⟩
  have heq :
      ((StructuralRamsey.Partite.System.inclusion C
        (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding.comp a) =
        proj.val := by
    apply RelStructure.Embedding.ext
    intro u
    exact (hProj u).symm
  calc
    T = copyCarrier
        ((StructuralRamsey.Partite.System.inclusion C
          (activeCarrier A₀.ordered C β.toFunctionEmbedding)).toEmbedding.comp a) := hEq
    _ = copyCarrier proj.val := congrArg copyCarrier heq

end StructuralRamsey.Girth
