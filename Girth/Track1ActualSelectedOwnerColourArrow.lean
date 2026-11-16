import Girth.Track1SelectedActualOwnerCopies
import Girth.Track1SelectedSupportColourArrow
import Girth.TrainColouredOwnerExactColourTransfer

/-!
# Numbered Track 1: the actual old selected-owner edge arrow

The EHN family yields a monochromatic selected B image for any colouring
of all A-embeddings. The old owner-split support contains ONLY the
positive A-support edges belonging to selected B images.

This theorem converts the EHN selected-embedding arrow to the exact
old physical-edge arrow used by the checked selectedColourTransfer
lemma. It uses no edge-coveredness of the original EHN witness and
does not prune edges during the subsequent recursive partite construction.

This is a staged, uncompiled integration candidate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB V I Choice : Type v}

/-- The selected physical B supports satisfy the full old edge-colour
Ramsey arrow, without declaring this as a new hypothesis. -/
theorem actualSelectedOwner_oldColourArrow
    (A : RelStructure L UA)
    {B : RelStructure L VB} {C : RelStructure L V}
    (family : Choice → Embedding B C)
    (predicate : V → I) (allowed : Set I)
    {κ : Type w} [Nonempty κ]
    (hSelectedArrow : ∀ χ : Embedding A C → κ,
      ∃ c : Choice, ∀ a b : Embedding A B,
        χ ((family c).comp a) = χ ((family c).comp b))
    (hForbidden : ∀ c : Choice, ∀ (w : VB)
      (e f : {e : Set VB // e ∈ supportCopies A B}),
      predicate (family c w) ∉ allowed →
      w ∈ e.1 → w ∈ f.1 → e = f)
    (χ : (selectedSupportOwnerSystem A family predicate allowed).OldEdge → κ) :
    ∃ c : Choice,
      ∀ e f : (actualSelectedOwnerCopy A family predicate allowed
        c (hForbidden c)).SourceEdge,
        χ ((actualSelectedOwnerCopy A family predicate allowed
          c (hForbidden c)).physicalEdge e) =
        χ ((actualSelectedOwnerCopy A family predicate allowed
          c (hForbidden c)).physicalEdge f) := by
  classical
  let H := selectedSupportOwnerSystem A family predicate allowed
  let S : Choice → ColouredOwnerSelectedCopy (W := VB) H :=
    fun c => actualSelectedOwnerCopy A family predicate allowed
      c (hForbidden c)
  have hOld :
      ∀ c : Choice, ∀ e : (S c).SourceEdge,
        ∀ a : Embedding A B,
        e.1 = copyCarrier a →
        ((S c).physicalEdge e).1 =
          copyCarrier ((family c).comp a) := by
    intro c e a he
    change (family c).toFunctionEmbedding '' e.1 =
      copyCarrier ((family c).comp a)
    rw [he]
    exact (copyCarrier_comp_eq_image (family c) a).symm
  obtain ⟨c, hc⟩ :=
    selectedSupportEdges_colourArrow A family hSelectedArrow
      (fun e : SelectedSupportEdge A family => χ e)
  refine ⟨c, ?_⟩
  intro e f
  have he : e.1 ∈ supportCopies A B := e.2
  have hf : f.1 ∈ supportCopies A B := f.2
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hf
  let eOld : SelectedSupportEdge A family :=
    ⟨copyCarrier ((family c).comp a), ⟨c, a, rfl⟩⟩
  let fOld : SelectedSupportEdge A family :=
    ⟨copyCarrier ((family c).comp b), ⟨c, b, rfl⟩⟩
  have heEq : (S c).physicalEdge e = eOld := by
    apply Subtype.ext
    exact hOld c e a ha
  have hfEq : (S c).physicalEdge f = fOld := by
    apply Subtype.ext
    exact hOld c f b hb
  change χ ((S c).physicalEdge e) = χ ((S c).physicalEdge f)
  calc
    χ ((S c).physicalEdge e) = χ eOld := congrArg χ heEq
    _ = χ fOld := hc a b
    _ = χ ((S c).physicalEdge f) := (congrArg χ hfEq).symm

#print axioms StructuralRamsey.Girth.actualSelectedOwner_oldColourArrow

end StructuralRamsey.Girth
