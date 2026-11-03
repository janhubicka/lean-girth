import Girth.TrainFillingTemplateConstruction

set_option Elab.async false

/-!
# Colour words on the actual physical edges of a uniform filling

Section 16 colours an old edge f by the function on local template edges
e ↦ χ(ι_f[e]). We use UniformFillingData.edgeEquiv, not a chosen ordering
of local edges or an arbitrary quotient of the physical edge family.

The pairing is genuinely bijective, so the word captures every filled
physical edge exactly once. The local Ramsey choice of a monochromatic
W* can then be transported through the same word on every old edge in
the chosen M-copy.

This is the colour calculation, NOT the construction of X, the N-copy
of M, or the embedding of the selected G0 target inside the final H.
-/

namespace StructuralRamsey.Girth.UniformFillingData

universe v w

variable {V X : Type v} (U : UniformFillingData V X)
variable {κ : Type w}

/-- The fixed-coordinate colour word of the filled edges over old edge f. -/
noncomputable def colourWord
    (χ : U.toTrainFilling.NewEdge → κ) (f : U.OldEdge) :
    U.TemplateEdge → κ :=
  fun e => χ (U.edgeEquiv (f, e))

@[simp] theorem colourWord_apply
    (χ : U.toTrainFilling.NewEdge → κ) (f : U.OldEdge)
    (e : U.TemplateEdge) :
    U.colourWord χ f e = χ (U.edgeEquiv (f, e)) := rfl

/-- Every actual filled physical edge occurs in the word above its unique
old cover. No omitted or duplicated physical labels are possible. -/
theorem colourWord_complete
    (χ : U.toTrainFilling.NewEdge → κ)
    (e : U.toTrainFilling.NewEdge) :
    U.colourWord χ (U.edgeEquiv.symm e).1 (U.edgeEquiv.symm e).2 = χ e := by
  change χ (U.edgeEquiv (U.edgeEquiv.symm e)) = χ e
  rw [Equiv.apply_symm_apply]

/-- Equality of old-edge colours is equality of the entire local word,
not merely equality of a selected local edge's colour. -/
theorem colourWord_eq_at
    (χ : U.toTrainFilling.NewEdge → κ)
    (f g : U.OldEdge)
    (h : U.colourWord χ f = U.colourWord χ g)
    (e : U.TemplateEdge) :
    χ (U.edgeEquiv (f, e)) = χ (U.edgeEquiv (g, e)) := by
  exact congrFun h e

/-- The two Ramsey arrows combine without any choice-dependent ordering:
one constant word on the old copy and one monochromatic selected local
W* produce a monochromatic set of actual filled physical edges. -/
theorem colourWord_selected_monochromatic
    (χ : U.toTrainFilling.NewEdge → κ)
    (S : Set U.OldEdge) (T : Set U.TemplateEdge)
    (ρ : U.TemplateEdge → κ) (colour : κ)
    (hWords : ∀ f, f ∈ S → U.colourWord χ f = ρ)
    (hLocal : ∀ e, e ∈ T → ρ e = colour) :
    ∀ f, f ∈ S → ∀ e, e ∈ T →
      χ (U.edgeEquiv (f, e)) = colour := by
  intro f hf e he
  calc
    χ (U.edgeEquiv (f, e)) = U.colourWord χ f e := rfl
    _ = ρ e := congrFun (hWords f hf) e
    _ = colour := hLocal e he

/-- Equivalently, the local Ramsey choice can be made after the old-edge
Ramsey arrow has selected one common word. The selected family of local
edge sets is not assumed to be singleton or independent of the word. -/
theorem colourWord_selected_exists
    (χ : U.toTrainFilling.NewEdge → κ)
    (S : Set U.OldEdge)
    (family : Set (Set U.TemplateEdge))
    (ρ : U.TemplateEdge → κ)
    (hWords : ∀ f, f ∈ S → U.colourWord χ f = ρ)
    (hLocalRamsey :
      ∃ T, T ∈ family ∧ ∃ colour : κ, ∀ e, e ∈ T → ρ e = colour) :
    ∃ T, T ∈ family ∧ ∃ colour : κ,
      ∀ f, f ∈ S → ∀ e, e ∈ T →
        χ (U.edgeEquiv (f, e)) = colour := by
  obtain ⟨T, hT, colour, hLocal⟩ := hLocalRamsey
  exact ⟨T, hT, colour,
    U.colourWord_selected_monochromatic χ S T ρ colour hWords hLocal⟩

/-- There are precisely r raised to the number of local template edges
possible word colours, including when the local edge family is empty. -/
theorem colourWord_palette_card [Fintype U.TemplateEdge] [Fintype κ] :
    Fintype.card (U.TemplateEdge → κ) =
      Fintype.card κ ^ Fintype.card U.TemplateEdge := by
  exact Fintype.card_fun

end StructuralRamsey.Girth.UniformFillingData
