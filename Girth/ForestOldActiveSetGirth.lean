import Girth.ForestOldActiveGirth
import Girth.ForestFiniteSetCompletion

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

end StructuralRamsey.Girth
