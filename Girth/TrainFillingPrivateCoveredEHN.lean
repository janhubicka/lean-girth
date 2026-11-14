import Girth.TrainFillingPrivateMonotoneExistence

set_option Elab.async false

/-!
# Retain only the vertices actually covered by EHN A-support edges

The abstract ElementaryCAClass of a functional EHN witness proves
A-linearity and the canonical binary closure, not coverage of
EVERY vertex by an A-copy. The manuscript's canonical filling
explicitly needs the local X-template with NO isolated vertices.

The support-covered vertex set is the union of ALL actual A-copy
carriers. It has no uncovered vertices by definition. Moreover
EVERY selected copy of the target W lies entirely in it whenever
the source W is A-covered, because each A-copy in W composes with
the selected W -> X embedding.

Therefore trimming unused vertices after the EHN arrow is
mathematically legitimate for the selected W family. This file
only proves those actual containment and coverage facts; it does
NOT pretend the full induced-reduct Ramsey arrow or closure
structure has already been transported to the trimmed type.
That final retyping is a separate pending application step.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

/-- Exactly the vertices belonging to at least one genuine
relational A-support copy, not an invented cover of isolated
template vertices. -/
def supportCoveredVertices
    {L : RelLanguage.{u}} {UA X : Type v}
    (A : RelStructure L UA) (R : RelStructure L X) : Set X :=
  {x | ∃ a : Embedding A R, x ∈ copyCarrier a}

/-- Every A-support edge is contained in the supported vertex
reduct, so trimming does not remove any physical A-support
edge or any of its vertices. -/
theorem supportCopies_subset_coveredVertices
    {L : RelLanguage.{u}} {UA X : Type v}
    (A : RelStructure L UA) (R : RelStructure L X)
    (e : Set X) (he : e ∈ supportCopies A R) :
    e ⊆ supportCoveredVertices A R := by
  obtain ⟨a, ha⟩ := he
  intro x hx
  exact ⟨a, by rw [← ha]; exact hx⟩

/-- Every retained X-position is actually contained in a
template A-support edge; no artificial coverage hypothesis
on the original EHN output is used. -/
theorem supportCoveredVertices_is_covered
    {L : RelLanguage.{u}} {UA X : Type v}
    (A : RelStructure L UA) (R : RelStructure L X)
    (x : X) (hx : x ∈ supportCoveredVertices A R) :
    ∃ e : {e : Set X // e ∈ supportCopies A R},
      x ∈ e.1 := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨⟨copyCarrier a, ⟨a, rfl⟩⟩, ha⟩

/-- Crucial link for the Ramsey witness: the image of ANY
relationally selected W-copy lies inside the supported X
positions if every vertex of W is in some A-copy. All
individual first-wagon summands then survive the trim
simultaneously, because they all come from this SAME W-copy. -/
theorem selectedCoveredUnion_range_subset
    {L : RelLanguage.{u}} {UA W X : Type v}
    (A : RelStructure L UA)
    (B : RelStructure L W)
    (R : RelStructure L X)
    (selected : Embedding B R)
    (hBCovered : ∀ w : W,
      ∃ a : Embedding A B, w ∈ copyCarrier a) :
    copyCarrier selected ⊆ supportCoveredVertices A R := by
  rintro z ⟨w, hw⟩
  obtain ⟨a, ha⟩ := hBCovered w
  obtain ⟨u, hu⟩ := ha
  have hz :
      z ∈ copyCarrier (selected.comp a) := by
    refine ⟨u, ?_⟩
    change selected (a u) = z
    exact (congrArg selected hu).trans hw
  exact ⟨selected.comp a, hz⟩

/-- The supported vertex subtype remains finite when the EHN
template X was finite. -/
theorem finite_supportCoveredVertices
    {L : RelLanguage.{u}} {UA X : Type v}
    (A : RelStructure L UA) (R : RelStructure L X)
    [Finite X] :
    Finite {x : X // x ∈ supportCoveredVertices A R} := by
  infer_instance

end StructuralRamsey.Girth
