import Girth.ForestOldActiveGirth
import Girth.ForestCopySetCompletion
import Girth.ForestCompletionTwoEdgeLinearity

/-!
# Actual finite-copy-set completion implies old active girth

The manuscript tests finite SETS of genuine A- and designated
B-copies. Map each such copy to its complete A-support piece.
The map need not be injective. A finite labelled completion of
these actual copies gives the existing indexed
`ForestCompletionProperty`, using the finite image of chosen
copy labels and without arbitrary subforest heredity.

The final theorem needs only this direction of transport. For
m >= 2, the very same completion invariant already forces
ambient A-linearity by completing each pair of different
one-edge A-supports. We thus derive the old active subsystem's
girth without assuming that linearity separately.

This is a source-level proof candidate. Do not treat it as
Lean-verified before exact-head compilation and axiom auditing.
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

/-- For cutoff at least two, the active-subsystem girth conclusion
follows from the actual finite-copy-set completion invariant and
A-strongness of designated base projections WITHOUT separately
assuming old A-linearity.

Indeed every ambient A-edge is a tested one-edge member.
Completing a pair of distinct such members forces their
intersection to be subsingleton: added designated B-members
cannot make the two selected edge members pairwise allowed if
they intersect in two vertices. Hence old A-linearity follows
from the same completion invariant already used for active girth. -/
theorem oldActiveInduced_girthGT_of_actualCopySets_without_oldLinear
    (A : RelStructure L UA)
    (u w : UA) (huw : u ≠ w)
    (B : RelStructure L VB)
    (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (hBaseStrong :
      ∀ q : DesignatedCopy B D C family,
        AStrong A D (copyCarrier q.base))
    (m : ℕ) (hm : 2 ≤ m)
    (hCopySetCompletion :
      FinsetLabelForestCompletionProperty
        (pictureABLabelSupport A B D C family)
        (fun _ => True)
        (designatedPictureASupport A B D C family) m) :
    GirthGT
      (supportCopies A
        (C.induce
          (activeCarrier A C e.toFunctionEmbedding)).toRelStructure) m := by
  classical
  have hComplete :
      ForestCompletionProperty
        (testedPictureABSupport A B D C family)
        (designatedPictureASupport A B D C family) m := by
    apply hCopySetCompletion.toSupportIndexed
    intro T hT
    obtain ⟨label, hLabel⟩ :=
      (testedPictureABSupport_iff_label A B D C family T).mp hT
    exact ⟨label, trivial, hLabel⟩
  have hLinear :
      LinearEdgeSet (supportCopies A C.toRelStructure) :=
    linearEdgeSet_of_twoEdgeForestCompletion
      (supportCopies A C.toRelStructure)
      (testedPictureABSupport A B D C family)
      (designatedPictureASupport A B D C family)
      m hm hComplete
      (by
        intro z hz
        obtain ⟨a, ha⟩ := hz
        left
        exact ⟨a, congrArg HypergraphPiece.oneEdge ha⟩)
  have hOldLinear : ALinear A C.toRelStructure := by
    intro a b hDifferent
    exact hLinear ⟨a, rfl⟩ ⟨b, rfl⟩ hDifferent
  exact oldActiveInduced_girthGT_of_designatedCompletion
    A u w huw B D C family e hOldLinear hBaseStrong
    m hComplete

end StructuralRamsey.Girth
