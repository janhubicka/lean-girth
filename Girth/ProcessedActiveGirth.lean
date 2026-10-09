import Girth.ProcessedCoreProjection
import Girth.SupportGirthEmbeddingEquiv

/-!
# Girth of the processed active subsystem

The active gluing subsystem is the union of the old A-copies with the
processed projection alpha. After a standard attachment, *every*
new A-copy with projection alpha lies in the local core (the preceding
module).

Consequently every vertex of the new active alpha-carrier lies in the
core. Because the core is an induced relational substructure, the
entire induced new alpha-subsystem embeds back into the local witness.
The induced subsystem's A-support is thus a subfamily of the witness
A-support, transported through an embedding. Reflecting girth through
that embedding proves the desired bound.

No local Ramsey arrow, foresthood, base linearity, or A-generation
hypothesis is needed for this core-side girth argument. The essential
geometric hypothesis is that the old gluing subsystem is the TRUE
active A-carrier, together with irreducibility of A.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- The processed active vertex set of a standard picture extension
is contained in the actual local core. -/
theorem processedActiveCarrier_subset_core
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E) :
    activeCarrier A
      (StructuralRamsey.Partite.Attachment.attach C
        (activeCarrier A C α) E f) α ⊆
    copyCarrier
      (StructuralRamsey.Partite.Attachment.coreEmbedding C
        (activeCarrier A C α) E f).toEmbedding := by
  intro z hz
  obtain ⟨a, ⟨u, hu⟩⟩ := hz
  obtain ⟨y, hy⟩ :=
    processedProjectedACopy_in_core A hA C α E f a u
  exact ⟨y, hu.symm.trans hy⟩

/-- The full A-support of the ACTUAL processed active subsystem has
girth >g whenever the local core witness does. This is a genuine
induced-subsystem result, not merely a statement about labelled
projected edge occurrences. -/
theorem processed_activeSubsystem_girthGT_of_local
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (g : ℕ)
    (hGirthE : GirthGT (supportCopies A E.toRelStructure) g) :
    GirthGT
      (supportCopies A
        ((StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C α) E f).induce
            (activeCarrier A
              (StructuralRamsey.Partite.Attachment.attach C
                (activeCarrier A C α) E f) α)).toRelStructure) g := by
  classical
  let S := activeCarrier A C α
  let W := StructuralRamsey.Partite.Attachment.attach C S E f
  let T := activeCarrier A W α
  let incl : RelStructure.Embedding (W.induce T).toRelStructure
      W.toRelStructure :=
    (StructuralRamsey.Partite.System.inclusion W T).toEmbedding
  let core : RelStructure.Embedding E.toRelStructure
      W.toRelStructure :=
    (StructuralRamsey.Partite.Attachment.coreEmbedding C S E f).toEmbedding
  have hCore : T ⊆ copyCarrier core :=
    processedActiveCarrier_subset_core A hA C α E f
  have hInto : ∀ t : T, ∃ y : Y, incl t = core y := by
    intro t
    exact hCore t.2
  let back : RelStructure.Embedding (W.induce T).toRelStructure
      E.toRelStructure :=
    incl.factorThroughRange core hInto
  have hMapSub :
      mappedSupportCopies A (W.induce T).toRelStructure
        E.toRelStructure back ⊆ supportCopies A E.toRelStructure := by
    rintro e ⟨a, rfl⟩
    exact ⟨back.comp a, rfl⟩
  have hMapped :
      GirthGT (mappedSupportCopies A (W.induce T).toRelStructure
        E.toRelStructure back) g :=
    girthGT_of_subset hMapSub hGirthE
  exact girthGT_source_of_mappedSupportCopies
    A (W.induce T).toRelStructure E.toRelStructure
    back g hMapped

end StructuralRamsey.Girth
