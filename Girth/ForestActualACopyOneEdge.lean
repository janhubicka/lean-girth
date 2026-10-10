import Girth.ForestRelationalBoundarySupport
import Girth.ForestCompletionSeparatorRequests

/-!
# The complete A-support of a genuine finite A-copy is one-edge

Selected A-copies are represented in the circulation mixed forest as
one-edge support pieces. This must agree with the COMPLETE
A-subcopy support of the actual relational embedding used for B-copies.

Every self-embedding of a finite A is surjective, so all A-subcopies
of an embedded A-copy have the same image carrier. Consequently the
support piece has exactly its own carrier as its sole support edge.
This identifies the A-member representation with the one-edge
piece used by the mixed forest and auxiliary deletion lemmas.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA W : Type v}

/-- The complete A-support of one actual embedded finite A-copy
consists of precisely its whole carrier edge. -/
theorem embeddedACopySupportPiece_self_isOneEdge
    [Finite UA]
    (A : RelStructure L UA)
    {D : RelStructure L W}
    (b : RelStructure.Embedding A D) :
    (embeddedACopySupportPiece A b).IsOneEdge := by
  classical
  have hSurj (a : RelStructure.Embedding A A) :
      Function.Surjective a :=
    Finite.injective_iff_surjective.mp a.injective
  have hCarrier (a : RelStructure.Embedding A A) :
      copyCarrier (b.comp a) = copyCarrier b := by
    apply Set.Subset.antisymm
    · rintro x ⟨u, rfl⟩
      exact ⟨a u, rfl⟩
    · rintro x ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hSurj a u
      exact ⟨v, by simpa [hv]⟩
  change
    {e : Set W | ∃ a : RelStructure.Embedding A A,
      e = copyCarrier (b.comp a)} = {copyCarrier b}
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.mem_singleton_iff.mpr (hCarrier a)
  · intro he
    refine ⟨RelStructure.Embedding.id A, ?_⟩
    simpa only [RelStructure.Embedding.comp_id] using
      (Set.mem_singleton_iff.mp he)

/-- Thus the fully supported actual A-copy is exactly the formal
one-edge piece on its carrier, not merely carrier-contained in one. -/
theorem embeddedACopySupportPiece_self_eq_oneEdge
    [Finite UA]
    (A : RelStructure L UA)
    {D : RelStructure L W}
    (b : RelStructure.Embedding A D) :
    embeddedACopySupportPiece A b =
      HypergraphPiece.oneEdge (copyCarrier b) := by
  cases h : embeddedACopySupportPiece A b with
  | mk carrier edges hsub =>
      have hCarrier : carrier = copyCarrier b := by
        simpa [h] using (embeddedACopySupportPiece_carrier A b)
      have hEdges : edges = {carrier} := by
        simpa [h, HypergraphPiece.IsOneEdge] using
          (embeddedACopySupportPiece_self_isOneEdge A b)
      cases hCarrier
      cases hEdges
      rfl

end StructuralRamsey.Girth
