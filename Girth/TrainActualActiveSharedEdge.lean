import Girth.ActivePicture
import Girth.TrainActualSharedACarrierSubfamily

/-!
# Genuine nonempty shared A-edge at every active picture step

The generated train root class is universal only when the core meets
every attached standard picture in an ACTUAL shared A-support edge.

In the circulation induction, the active gluing subsystem is the
union of the carriers of projected A-copies. If at least one such
copy exists, its entire physical A-support carrier belongs to the
active subsystem and is therefore a genuine shared old A-edge.
The same shared edge is carried by every standard-copy embedding.

Thus the top-contact hypothesis is automatic at every nonempty
active fibre; empty fibres are skipped, not handled by fictitious
shared edge labels. No local designated B-coverage assumption is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- A complete old A-copy lying in the gluing subsystem yields a
genuine SHARED old A-carrier edge. -/
theorem sharedOldACarrier_nonempty_of_oldCopy
    (A : RelStructure L UA)
    (B : RelStructure L X)
    (S : Set X)
    (a : RelStructure.Embedding A B)
    (hRange : copyCarrier a ⊆ S) :
    Nonempty (SharedOldACarrierEdge A B S) := by
  let T : OldACarrierEdge A B :=
    ⟨copyCarrier a, ⟨a, rfl⟩⟩
  exact ⟨⟨T, hRange⟩⟩

/-- Every nonempty projected A-fibre supplies the ACTUAL nonempty
shared-edge condition required by the generated train's top cut. -/
theorem activeCarrier_has_sharedOldAEdge
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P)
    (e : StructuralRamsey.Partite.ProjectedEmbedding A C α) :
    Nonempty
      (SharedOldACarrierEdge A C.toRelStructure
        (activeCarrier A C α)) := by
  apply sharedOldACarrier_nonempty_of_oldCopy
    A C.toRelStructure (activeCarrier A C α) e.val
  rintro x ⟨a, ha⟩
  exact ⟨e, ⟨a, ha⟩⟩

/-- Reuse the genuine shared-edge witness uniformly for every
standard-copy index. There is no additional per-index geometry
when all standard copies are attached along the same active fibre. -/
theorem activeCarrier_all_standard_copies_meet_core
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P)
    (e : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (I : Type v) :
    ∀ _i : I,
      Nonempty
        (SharedOldACarrierEdge A C.toRelStructure
          (activeCarrier A C α)) := by
  intro _
  exact activeCarrier_has_sharedOldAEdge A C α e

end StructuralRamsey.Girth
