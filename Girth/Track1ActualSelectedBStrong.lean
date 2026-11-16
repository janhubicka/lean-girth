import Girth.Track1ActualSelectedCoverage
import Girth.Track1SelectedOldStrong

/-!
# Track 1: every genuinely selected lifted B image is edge-strong

The checked owner-splitting strongness kernel requires:
* each retained old physical edge is a true ambient A-copy;
* each source A-copy belongs to the selected B-source support;
* the old selected B image is A-strong.

All three are derived from the concrete selected EHN support union.
Thus a split edge meeting the selected lifted B-image in two
different vertices belongs to that B-image's exact source edge set.

DRAFT: no exact-head Lean kernel check yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB V I Choice : Type v}

/-- Strong inducedness of an actual selected B image, expressed
as exact physical split-edge ownership. In particular the output
strongness is NOT separately assumed after the vertex splitting. -/
theorem track1_actualSelectedBStrong_from_old
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    (hForbidden : ∀ c : Choice, ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f)
    (hStrong : ∀ c : Choice,
      AStrong A C (copyCarrier (family c))) :
    let H := selectedSupportOwnerSystem A family predicate allowed
    let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
      fun c => actualSelectedOwnerCopy A family predicate allowed c
        (hForbidden c)
    ∀ c : Choice, ∀ f : H.OldEdge, ∀ z w : H.Vertex,
      z ≠ w → z ∈ H.splitEdge f → w ∈ H.splitEdge f →
      z ∈ Set.range (selected c).lift →
      w ∈ Set.range (selected c).lift →
      ∃ a : (selected c).SourceEdge, (selected c).physicalEdge a = f := by
  classical
  dsimp
  let H := selectedSupportOwnerSystem A family predicate allowed
  let selected : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
    fun c => actualSelectedOwnerCopy A family predicate allowed c
      (hForbidden c)
  have hSupport : ∀ f : H.OldEdge,
      ∃ a : Embedding A C, f.1 = copyCarrier a := by
    intro f
    obtain ⟨c, a, h⟩ := f.2
    exact ⟨(family c).comp a, h⟩
  intro c f z w hzw hz hw hzCopy hwCopy
  have hEmbed : ∀ x : VB, (selected c).embedding x = (family c) x := by
    intro x
    rfl
  have hSrc : ∀ a : Embedding A B,
      copyCarrier a ∈ (selected c).sourceEdges := by
    intro a
    exact ⟨a, rfl⟩
  exact ColouredOwnerSelectedCopy.selected_strong_of_aStrong
    A B C H (selected c) (family c)
    hEmbed hSupport hSrc (hStrong c)
    f z w hzw hz hw hzCopy hwCopy

#print axioms StructuralRamsey.Girth.track1_actualSelectedBStrong_from_old

end StructuralRamsey.Girth
