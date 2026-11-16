import Girth.Support
import Mathlib.Tactic

/-!
# Numbered Track 1: actual selected SUPPORT-edge Ramsey arrow

The EHN arrow colours embeddings of the one-edge type A in its entire
ambient relational witness. The owner split needs an edge-colouring
arrow on the *positive support union* of the selected B images.

No non-selected edge is inserted into this union. A colouring of the
union is extended arbitrarily to all ambient A-embeddings and the
original selected-family arrow is applied. This is the exact
bookkeeping behind the manuscript's "discard unused edges".

The selected-family arrow is an explicit INPUT; constructing that
family via triangle-free EHN is provided by the separate branch's
Track1TriangleFreeSelectedFamily.

STAGED DRAFT, not yet kernel-compiled.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB V Choice : Type v}

/-- The actual A-support edge carriers used inside the designated
selected B target images; an ambient edge outside the union is omitted. -/
def selectedSupportEdges
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C) : Set (Set V) :=
  {E | ∃ c : Choice, ∃ a : Embedding A B,
    E = copyCarrier ((family c).comp a)}

/-- A physical positive edge with evidence that it belongs to at
least one genuinely selected target image. -/
abbrev SelectedSupportEdge
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C) :=
  {E : Set V // E ∈ selectedSupportEdges A family}

/-- Any old colouring of selected positive support edges extends to
a colouring of ALL A-embeddings of the EHN ambient structure.  The
chosen monochromatic B image is part of the same indexed family;
there is no extra assumption that the whole ambient witness is
covered by selected B targets. -/
theorem selectedSupportEdges_colourArrow
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    {κ : Type w} [Nonempty κ]
    (hSelectedArrow :
      ∀ χ : Embedding A C → κ,
        ∃ c : Choice, ∀ a b : Embedding A B,
          χ ((family c).comp a) = χ ((family c).comp b))
    (χ : SelectedSupportEdge A family → κ) :
    ∃ c : Choice, ∀ a b : Embedding A B,
      χ ⟨copyCarrier ((family c).comp a), ⟨c, a, rfl⟩⟩ =
      χ ⟨copyCarrier ((family c).comp b), ⟨c, b, rfl⟩⟩ := by
  classical
  let χext : Embedding A C → κ := fun a =>
    if h : copyCarrier a ∈ selectedSupportEdges A family then
      χ ⟨copyCarrier a, h⟩
    else
      Classical.choice inferInstance
  obtain ⟨c, hc⟩ := hSelectedArrow χext
  refine ⟨c, ?_⟩
  intro a b
  have ha : copyCarrier ((family c).comp a) ∈
      selectedSupportEdges A family := ⟨c, a, rfl⟩
  have hb : copyCarrier ((family c).comp b) ∈
      selectedSupportEdges A family := ⟨c, b, rfl⟩
  simpa [χext, ha, hb] using hc a b

#print axioms StructuralRamsey.Girth.selectedSupportEdges_colourArrow

end StructuralRamsey.Girth
