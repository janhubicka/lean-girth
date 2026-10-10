import Girth.ForestRelationalBoundarySupport

/-!
# Exact mapped local-core membership of a classified A-support edge

If the boundary between an embedded B-copy and an embedded core
is an A-copy inside B, that boundary A-copy is contained in the
core image and therefore factors uniquely through the core
embedding. Thus its carrier is one of the ACTUAL mapped core
A-support edges. No separate local-support membership promise is
necessary.

This is the missing geometry for applying the complete abstract
all-distinct forest theorem to relational A/B support pieces.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB Y W : Type v}

/-- An A-copy contained in the core image factors through its
embedding; in particular its carrier is an edge of the mapped
A-support of the core. -/
theorem embeddedACopy_mem_mappedCoreSupport
    (A : RelStructure L UA)
    {D : RelStructure L Y} {E : RelStructure L W}
    (core : RelStructure.Embedding D E)
    (a : RelStructure.Embedding A E)
    (hInside : copyCarrier a ⊆ copyCarrier core) :
    copyCarrier a ∈
      {e : Set W | ∃ aD : RelStructure.Embedding A D,
        e = copyCarrier (core.comp aD)} := by
  classical
  have hFactor (u : UA) :
      ∃ z : Y, a u = core z := by
    obtain ⟨z, hz⟩ := hInside ⟨u, rfl⟩
    exact ⟨z, hz.symm⟩
  let aD : RelStructure.Embedding A D :=
    a.factorThroughRange core hFactor
  have hSpec (u : UA) : a u = core (aD u) :=
    Classical.choose_spec (hFactor u)
  refine ⟨aD, ?_⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, (hSpec u).symm⟩
  · rintro ⟨u, hx⟩
    exact ⟨u, (hSpec u).trans hx⟩

/-- An actual B-copy's carrier intersection with the core is
subsingleton or a COMPLETE local A-support edge belonging to the
selected B-piece's OWN A-support. This discharges BOTH support-edge
memberships needed in SmallOrWholeEdgeBoundary. -/
theorem embeddedACopySupportPiece_boundary_of_core
    (A : RelStructure L UA)
    {B : RelStructure L VB}
    {D : RelStructure L Y} {E : RelStructure L W}
    (core : RelStructure.Embedding D E)
    (b : RelStructure.Embedding B E)
    (hClassify :
      (copyCarrier b ∩ copyCarrier core).Subsingleton ∨
        ∃ a : RelStructure.Embedding A B,
          copyCarrier b ∩ copyCarrier core =
            copyCarrier (b.comp a)) :
    SmallOrWholeEdgeBoundary
      {e : Set W | ∃ aD : RelStructure.Embedding A D,
        e = copyCarrier (core.comp aD)}
      (copyCarrier core)
      (embeddedACopySupportPiece A b) := by
  apply embeddedACopySupportPiece_smallOrWholeBoundary
    A b (copyCarrier core)
    {e : Set W | ∃ aD : RelStructure.Embedding A D,
      e = copyCarrier (core.comp aD)}
    hClassify
  intro a ha
  apply embeddedACopy_mem_mappedCoreSupport A core (b.comp a)
  intro x hx
  have hBoundary : x ∈ copyCarrier b ∩ copyCarrier core := by
    rw [ha]
    exact hx
  exact hBoundary.2

end StructuralRamsey.Girth
