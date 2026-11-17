import Girth.Track1SelectedActualOwnerCopies
import Girth.Support

/-!
# Track 1: source forbidden-part degree-one is not an extra hypothesis

The manuscript assumes that distinct source A-edges may intersect only
in the allowed unary predicate blocks. This implies the exact
forbidden-vertex unique-edge condition required by the checked
owner-splitting constructor.

For a selected B embedding, unary predicate preservation transfers
the source degree-one property to the old target predicate.
This eliminates any independently postulated owner uniqueness.

Staged draft; no exact-head kernel check yet.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- The standard source edge-intersection restriction is precisely what
ensures that each forbidden vertex belongs to at most one source edge. -/
theorem track1_forbiddenDegreeOne_of_allowedIntersections
    (edges : Set (Set VB))
    (sourceColour : VB → I) (allowed : Set I)
    (hRestricted : ∀ e f : Set VB,
      e ∈ edges → f ∈ edges → e ≠ f →
      ∀ w : VB, w ∈ e → w ∈ f → sourceColour w ∈ allowed)
    (w : VB) (e f : {e : Set VB // e ∈ edges})
    (hForbidden : sourceColour w ∉ allowed)
    (hwe : w ∈ e.1) (hwf : w ∈ f.1) :
    e = f := by
  classical
  by_contra hne
  have hSets : e.1 ≠ f.1 := by
    intro h
    exact hne (Subtype.ext h)
  exact hForbidden (hRestricted e.1 f.1 e.2 f.2 hSets w hwe hwf)

/-- The same source restriction supplies the marked uniqueness premise
for EVERY selected embedding, using only its unary predicate preservation. -/
theorem track1_selectedForbiddenDegreeOne
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (sourceColour : VB → I)
    (predicate : V → I) (allowed : Set I)
    (hRestricted : ∀ e f : Set VB,
      e ∈ supportCopies A B → f ∈ supportCopies A B → e ≠ f →
      ∀ w : VB, w ∈ e → w ∈ f → sourceColour w ∈ allowed)
    (hPredicate : ∀ c : Choice, ∀ w : VB,
      predicate (family c w) = sourceColour w) :
    ∀ c : Choice, ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f := by
  intro c w e f hForb hwe hwf
  have hOldForbidden : sourceColour w ∉ allowed := by
    simpa only [hPredicate c w] using hForb
  exact track1_forbiddenDegreeOne_of_allowedIntersections
    (supportCopies A B) sourceColour allowed hRestricted
    w e f hOldForbidden hwe hwf

#print axioms StructuralRamsey.Girth.track1_forbiddenDegreeOne_of_allowedIntersections
#print axioms StructuralRamsey.Girth.track1_selectedForbiddenDegreeOne

end StructuralRamsey.Girth
