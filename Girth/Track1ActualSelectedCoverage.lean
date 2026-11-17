import Girth.Track1SelectedActualOwnerCopies
import Girth.Track1SelectedCarrierEmbedding
import Girth.TrainColouredOwnerSelectedStrong

/-!
# Track 1: all positive split edges lie in the truly used output carrier

The original EHN witness need not be covered by selected B-copies.
We retain only A-support edges IN selected images, and build the split
owner-token hypergraph from exactly that union. Every resulting
physical edge therefore has a genuine selected source A-edge owner.
This gives exact edge coverage by the union of the lifted selected
B-copy carriers, independently of any unused owner tokens.

The source marked-vertex degree-one hypotheses are the exact inputs
derived separately by Track1ForbiddenPartDegreeOne.

DRAFT: do not promote manuscript marks before exact-head Lean build.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB V I Choice : Type v}

namespace ColouredEdgeOwnerSplit

/-- Exact edge coverage for any *independently indexed* selected family.
The selected index Choice need not be the old unary predicate index I. -/
theorem selectedLiftCarrierFor_covers_splitEdge
    {W : Type v}
    (H : ColouredEdgeOwnerSplit V I)
    (selected : Choice → ColouredOwnerSelectedCopy (W := W) H)
    (hOldCover : ∀ f : H.OldEdge,
      ∃ c : Choice, ∃ a : (selected c).SourceEdge,
        (selected c).physicalEdge a = f)
    (f : H.OldEdge) :
    H.splitEdge f ⊆ H.selectedLiftCarrierFor selected := by
  obtain ⟨c, a, ha⟩ := hOldCover f
  intro z hz
  have hSelected : z ∈ Set.range (selected c).lift := by
    apply (selected c).split_selected_edge_subset_copy a
    rw [ha]
    exact hz
  exact ⟨c, hSelected⟩

end ColouredEdgeOwnerSplit

/-- Every retained old physical edge of the concrete selected-EHN
owner system is the image of an ACTUAL A-source edge in an ACTUAL
selected B embedding, without any separately assumed coverage. -/
theorem track1_actualSelectedOldEdge_covered
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (hForbidden : ∀ c : Choice, ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f) :
    ∀ f : (selectedSupportOwnerSystem A family predicate allowed).OldEdge,
      ∃ c : Choice,
        ∃ a : (actualSelectedOwnerCopy A family predicate allowed
          c (hForbidden c)).SourceEdge,
          (actualSelectedOwnerCopy A family predicate allowed
            c (hForbidden c)).physicalEdge a = f := by
  classical
  intro f
  obtain ⟨c, a, ha⟩ := f.2
  let edge : {e : Set VB // e ∈ supportCopies A B} :=
    ⟨copyCarrier a, ⟨a, rfl⟩⟩
  refine ⟨c, edge, ?_⟩
  apply Subtype.ext
  change (family c).toFunctionEmbedding '' copyCarrier a = f.1
  calc
    (family c).toFunctionEmbedding '' copyCarrier a =
        copyCarrier ((family c).comp a) :=
      (copyCarrier_comp_eq_image (family c) a).symm
    _ = f.1 := ha.symm

/-- The entire actual selected split-edge support is inside the
used selected-vertex carrier; no nonselected source edges or unused
owner tokens are added to the final coloured Ramsey witness. -/
theorem track1_actualSelectedSplitEdges_covered
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (hForbidden : ∀ c : Choice, ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f) :
    let H := selectedSupportOwnerSystem A family predicate allowed
    let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
      fun c => actualSelectedOwnerCopy A family predicate allowed
        c (hForbidden c)
    ∀ e : Set H.Vertex, e ∈ H.splitPhysicalEdges →
      e ⊆ H.selectedLiftCarrierFor selected := by
  classical
  dsimp
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
    fun c => actualSelectedOwnerCopy A family predicate allowed
      c (hForbidden c)
  have hCover : ∀ f : H.OldEdge,
      ∃ c : Choice, ∃ a : (selected c).SourceEdge,
        (selected c).physicalEdge a = f :=
    track1_actualSelectedOldEdge_covered
      A family predicate allowed hForbidden
  rintro e ⟨f, rfl⟩
  exact H.selectedLiftCarrierFor_covers_splitEdge selected hCover f

#print axioms StructuralRamsey.Girth.ColouredEdgeOwnerSplit.selectedLiftCarrierFor_covers_splitEdge
#print axioms StructuralRamsey.Girth.track1_actualSelectedOldEdge_covered
#print axioms StructuralRamsey.Girth.track1_actualSelectedSplitEdges_covered

end StructuralRamsey.Girth
