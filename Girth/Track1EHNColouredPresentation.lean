import Girth.Track1ColourFromRel
import Girth.Track1OldSelectedColouredPresentation

/-!
# Track 1: the exact old coloured EHN presentation needs no extra assumptions

The original source edge type is the k-vertex coloured ordered
one-edge structure. The selected target B is a genuine coloured
ordered hypergraph, enumerated edge by edge. The pre-existing
colouredOrderedEdgeSupport_exact theorem identifies its A-copy
hypergraph with its declared edge set.

For an arbitrary old EHN relational witness D, read a global colour
from the unary relations, using an arbitrary default on unused
vertices. All full selected B embeddings preserve those colours,
and the fresh auxiliary EHN order makes them monotone.

The exact positive union of selected A-supports therefore has actual
FULL induced old coloured ordered B embeddings, without assuming
an output predicate partition or a new edge relation axiom.

STAGED DRAFT, not kernel checked.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {I VB V Choice : Type v}

/-- Actual full induced selected B embeddings of the selected-positive
old hypergraph, obtained directly from the original EHN selected
family and the previously checked one-edge support identification. -/
noncomputable def track1_oldSelectedEHNColouredEmbedding
    (k : ℕ)
    (E : Set (Set VB))
    (sourceColourA : Fin k → I)
    (sourceColour : VB → I)
    [LinearOrder VB] [LinearOrder V]
    (hEnumerate : ∀ e ∈ E, ∃ ι : Fin k ↪ VB,
      Set.range (ι : Fin k → VB) = e ∧
      (∀ x, sourceColour (ι x) = sourceColourA x) ∧
      (∀ x y, sourceColourA x = sourceColourA y →
        (x < y ↔ ι x < ι y)))
    (D : RelStructure (colouredOrderedEdgeLanguage I k) V)
    (default : I)
    (family : Choice → Embedding
      (colouredOrderedEdgeTarget k E sourceColour) D)
    (c : Choice)
    (hMono : StrictMono (family c)) :
    Embedding
      (colouredOrderedEdgeTarget k E sourceColour)
      (colouredOrderedEdgeTarget k
        (selectedSupportEdges
          (colouredOrderedEdgeSource k sourceColourA) family)
        (oldColourOfRel D default)) := by
  classical
  let A := colouredOrderedEdgeSource k sourceColourA
  let B := colouredOrderedEdgeTarget k E sourceColour
  have hExact : supportCopies A B = E :=
    colouredOrderedEdgeSupport_exact k E
      sourceColourA sourceColour hEnumerate
  have hPredicate : ∀ w : VB,
      oldColourOfRel D default (family c w) = sourceColour w :=
    oldColourOfRel_on_selected k E sourceColour D default (family c)
  let e := track1_oldSelectedColouredOrderedEmbedding
    A family k sourceColour (oldColourOfRel D default)
      c hMono hPredicate
  change supportCopies A (colouredOrderedEdgeTarget k E sourceColour) = E at hExact
  simpa only [hExact] using e

#print axioms StructuralRamsey.Girth.track1_oldSelectedEHNColouredEmbedding

end StructuralRamsey.Girth
