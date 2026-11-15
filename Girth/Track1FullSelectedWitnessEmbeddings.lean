import Girth.Track1OldSelectedColouredPresentation
import Girth.Track1SelectedCarrierEmbedding
import Girth.Track1OwnerSplitFinite
import Girth.Track1ForbiddenPartDegreeOne

/-!
# Numbered Track 1: actual induced selected B copies on the covered split carrier

This combines:
* source forbidden degree-one from allowed edge-intersection predicates;
* canonical old selected owner copies from genuine B embeddings;
* induced old coloured ordered presentation, without assuming it;
* the checked global projection-first order;
* complete induced owner-split lifting;
* restriction to precisely the union of selected lifted B vertex ranges.

The source family is a genuine EHN family of B embeddings in the
unmarked canonical closure class. Its selected arrow, strongness,
controlled intersection, and triangle-free support are separate
prior inputs, not hidden assumptions here.

STAGED DRAFT, not exact-head kernel-compiled.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- The FULL actual ordered B-support embedding family in the genuine
selected, vertex-covered split hypergraph. None of its inducedness,
common order, or source owner labels is given as output data. -/
theorem track1_exists_actualSelectedColouredLifts
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    [LinearOrder VB] [LinearOrder V] [Finite V]
    (family : Choice → Embedding B C)
    (k : ℕ)
    (sourceColour : VB → I) (predicate : V → I)
    (allowed : Set I)
    (hRestricted : ∀ e f : Set VB,
      e ∈ supportCopies A B → f ∈ supportCopies A B → e ≠ f →
      ∀ w : VB, w ∈ e → w ∈ f → sourceColour w ∈ allowed)
    (hPredicate : ∀ c : Choice, ∀ w : VB,
      predicate (family c w) = sourceColour w)
    (hMono : ∀ c : Choice, StrictMono (family c)) :
    let H := selectedSupportOwnerSystem A family predicate allowed
    let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
      fun c => actualSelectedOwnerCopy A family predicate allowed
        c (track1_selectedForbiddenDegreeOne A family sourceColour
          predicate allowed hRestricted hPredicate c)
    ∃ o : LinearOrder H.Vertex,
      ∀ c : Choice,
        ∃ e : Embedding
          (colouredOrderedEdgeTarget k (supportCopies A B) sourceColour)
          ((@colouredOrderedEdgeTarget I H.Vertex k
            H.splitPhysicalEdges H.newPredicate o).induce
              (H.selectedLiftCarrierFor selected)),
          ∀ w : VB, (e w).1 = (selected c).lift w := by
  classical
  dsimp
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
    fun c => actualSelectedOwnerCopy A family predicate allowed
      c (track1_selectedForbiddenDegreeOne A family sourceColour
        predicate allowed hRestricted hPredicate c)
  haveI : Finite H.Vertex := H.finite_ownerVertex
  obtain ⟨o, ho⟩ := H.exists_projectionFirstLinearOrder
  refine ⟨o, ?_⟩
  intro c
  let bOld : Embedding
      (colouredOrderedEdgeTarget k (supportCopies A B) sourceColour)
      (colouredOrderedEdgeTarget k H.edges H.predicate) :=
    track1_oldSelectedColouredOrderedEmbedding
      A family k sourceColour predicate c (hMono c)
      (hPredicate c)
  have hMatch : ∀ w : VB, bOld w = (selected c).embedding w := by
    intro w
    rfl
  let bNew := H.actualSelectedEmbeddingOnCarrier
    o ho k sourceColour selected c bOld hMatch (hMono c)
  exact ⟨bNew, fun _ => rfl⟩

#print axioms StructuralRamsey.Girth.track1_exists_actualSelectedColouredLifts

end StructuralRamsey.Girth
