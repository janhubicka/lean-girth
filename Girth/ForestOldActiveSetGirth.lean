import Girth.ForestOldActiveGirth
import Girth.ForestFiniteSetCompletion
import Girth.ForestCopySetCompletion

/-!
# A finite-set interface for old active girth

The manuscript's forest-extension property is stated for finite
sets of selected A- and B-copy supports. The previous theorem uses
the indexed `ForestCompletionProperty` formalization. The generic
adapter `FinsetForestCompletionProperty.toIndexed` handles repeated
selected support pieces by taking the finite image; this yields the
same old-active-girth conclusion from a finite-set completion
hypothesis.

Caution: this is the exact support-piece set-to-index adapter.
The separate relational-copy-to-complete-A-support identification
still needs to be checked against the manuscript's copy convention.
No fresh Lean compilation is claimed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X : Type v}

/-- Labels of genuine selected A-copies and designated B-copies,
with their COMPLETE A-support as the output hypergraph piece. -/
def pictureABLabelSupport
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D)) :
    (RelStructure.Embedding A C.toRelStructure ⊕
      DesignatedCopy B D C family) → HypergraphPiece X
  | .inl a => HypergraphPiece.oneEdge (copyCarrier a)
  | .inr q => bSupportPiece A q.embedding

/-- The actual tested support predicate is exactly the image
of genuine mixed copy labels, without an injectivity assumption
on the map to complete support pieces. -/
theorem testedPictureABSupport_iff_label
    (A : RelStructure L UA)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (T : HypergraphPiece X) :
    testedPictureABSupport A B D C family T ↔
      ∃ label : RelStructure.Embedding A C.toRelStructure ⊕
          DesignatedCopy B D C family,
        pictureABLabelSupport A B D C family label = T := by
  constructor
  · intro hT
    rcases hT with ⟨a, ha⟩ | ⟨q, hq⟩
    · exact ⟨.inl a, ha.symm⟩
    · exact ⟨.inr q, hq.symm⟩
  · rintro ⟨label, hl⟩
    cases label with
    | inl a =>
        exact Or.inl ⟨a, hl.symm⟩
    | inr q =>
        exact Or.inr ⟨q, hl.symm⟩

theorem oldActiveInduced_girthGT_of_supportFinsetCompletion
    (A : RelStructure L UA)
    (u w : UA) (huw : u ≠ w)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (hOldLinear : ALinear A C.toRelStructure)
    (hBaseStrong :
      ∀ q : DesignatedCopy B D C family,
        AStrong A D (copyCarrier q.base))
    (m : ℕ)
    (hComplete :
      FinsetForestCompletionProperty
        (testedPictureABSupport A B D C family)
        (designatedPictureASupport A B D C family) m) :
    GirthGT
      (supportCopies A
        (C.induce
          (activeCarrier A C e.toFunctionEmbedding)).toRelStructure) m := by
  exact oldActiveInduced_girthGT_of_designatedCompletion
    A u w huw B D C family e
    hOldLinear hBaseStrong m hComplete.toIndexed

/-- The active-subsystem girth consequence of the manuscript's
forest-extension invariant stated on finite SETS of actual A- or
designated B-copy labels. No artificial injection from copies to
support pieces is assumed. The support forest is exactly the one
specified in the mixed A/B manuscript definitions. -/
theorem oldActiveInduced_girthGT_of_actualCopySets
    (A : RelStructure L UA)
    (u w : UA) (huw : u ≠ w)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (hOldLinear : ALinear A C.toRelStructure)
    (hBaseStrong :
      ∀ q : DesignatedCopy B D C family,
        AStrong A D (copyCarrier q.base))
    (m : ℕ)
    (hCopySetCompletion :
      FinsetLabelForestCompletionProperty
        (pictureABLabelSupport A B D C family)
        (fun _ => True)
        (designatedPictureASupport A B D C family) m) :
    GirthGT
      (supportCopies A
        (C.induce
          (activeCarrier A C e.toFunctionEmbedding)).toRelStructure) m := by
  have hSupportCompletion :
      ForestCompletionProperty
        (testedPictureABSupport A B D C family)
        (designatedPictureASupport A B D C family) m := by
    apply hCopySetCompletion.toSupportIndexed
    intro P hTest
    obtain ⟨label, hLabel⟩ :=
      (testedPictureABSupport_iff_label A B D C family P).mp hTest
    exact ⟨label, True.intro, hLabel⟩
  exact oldActiveInduced_girthGT_of_designatedCompletion
    A u w huw B D C family e
    hOldLinear hBaseStrong m hSupportCompletion

end StructuralRamsey.Girth
