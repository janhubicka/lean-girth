import Girth.ForestActualACopyOwner
import Girth.ActivePicture

/-!
# All A-copies of the processed projection lie in the new core

The standard picture step glues a local witness E into copies of
the old picture C along precisely the active subsystem C[alpha].

For an irreducible A, every attached A-copy lies in the core or
one full standard copy. If its projection is alpha and it lies in
a standard copy, its old preimage is an A-copy with projection alpha.
All vertices of that old copy belong to the active gluing carrier,
so the standard attachment identifies the entire new copy with
one in the core.

Thus every A-copy with the processed projection is in the new core.
This is the active-fibre half of the circulation girth invariant.
No Ramsey theorem or local forest statement is used here.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X Y I : Type v}

/-- Every A-copy with the processed projection alpha in an attachment
over the TRUE old active carrier is wholly contained in its core. -/
theorem processedProjectedACopy_in_core
    (A : RelStructure L UA)
    (hA : A.Irreducible)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) E)
    (a : StructuralRamsey.Partite.ProjectedEmbedding A
      (StructuralRamsey.Partite.Attachment.attach C
        (activeCarrier A C α) E f) α) :
    ∀ u : UA, ∃ y : Y,
      a.val u =
        (StructuralRamsey.Partite.Attachment.coreEmbedding
          C (activeCarrier A C α) E f) y := by
  classical
  let S := activeCarrier A C α
  let W := StructuralRamsey.Partite.Attachment.attach C S E f
  rcases attachment_aCopy_core_or_standard
      A hA C.toRelStructure S E.toRelStructure
      (fun i => (f i).toEmbedding) a.val with
    hCore | ⟨i, hStandard⟩
  · intro u
    exact hCore u
  · let std := StructuralRamsey.Partite.Attachment.copyEmbedding
        C S E f i
    let aOld : RelStructure.Embedding A C.toRelStructure :=
      a.val.factorThroughRange std.toEmbedding hStandard
    have hSpec (u : UA) : a.val u = std (aOld u) :=
      Classical.choose_spec (hStandard u)
    let aProjected : StructuralRamsey.Partite.ProjectedEmbedding A C α := {
      val := aOld
      property := by
        intro u
        calc
          C.part (aOld u) = W.part (std (aOld u)) :=
            (std.map_part (aOld u)).symm
          _ = W.part (a.val u) :=
            congrArg W.part (hSpec u).symm
          _ = α u := a.property u
    }
    intro u
    have huS : aOld u ∈ S :=
      projected_mem_activeCarrier A C α aProjected u
    refine ⟨f i ⟨aOld u, huS⟩, ?_⟩
    calc
      a.val u = std (aOld u) := hSpec u
      _ = (StructuralRamsey.Partite.Attachment.coreEmbedding
          C S E f) (f i ⟨aOld u, huS⟩) :=
        StructuralRamsey.Partite.Attachment.copy_extends
          C S E f i ⟨aOld u, huS⟩

end StructuralRamsey.Girth
