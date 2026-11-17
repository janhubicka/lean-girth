import Girth.ClosedPortProfiles

/-!
# Persistent profile colouring obstructs a reduct Ramsey arrow

If every selected B-embedding preserves a finite-valued invariant of
A-copies, and one B contains two A-copies of different invariant
values, colour each ambient A-copy by whether its invariant equals
that of the first copy. No selected B-embedding can be monochromatic.

This is the abstract reason that permanently naming construction
side/profile labels does NOT turn the three P4 birth packets into
an ordinary Ramsey proof for the side-forgetting reduct.

The theorem is a general algebraic obstruction with an explicit
two-colouring. It is not a no-go theorem for a construction that
allows the temporary side labels to be changed or forgotten under
the final Ramsey embedding.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe u

/-- An invariant preserved by all selected embeddings gives an
explicit persistent two-colouring of the coloured occurrences. -/
theorem exists_persistent_profile_colouring
    {AB BC AC T : Type u}
    (compose : BC → AB → AC)
    (typeB : AB → T) (typeC : AC → T)
    (hNaturality : ∀ b a, typeC (compose b a) = typeB a)
    (a₀ a₁ : AB)
    (hDifferent : typeB a₀ ≠ typeB a₁) :
    ∃ χ : AC → Bool,
      ∀ b : BC, χ (compose b a₀) ≠ χ (compose b a₁) := by
  classical
  refine ⟨(fun c => if typeC c = typeB a₀ then true else false), ?_⟩
  intro b
  change (if typeC (compose b a₀) = typeB a₀ then true else false) ≠
    (if typeC (compose b a₁) = typeB a₀ then true else false)
  rw [hNaturality b a₀, hNaturality b a₁]
  simp [hDifferent.symm]

/-- The same obstruction expressed as failure of the elementary
all-palette Ramsey arrow in its abstract embedding interface. -/
theorem no_monochromatic_selected_copy_of_two_profiles
    {AB BC AC T : Type u}
    (compose : BC → AB → AC)
    (typeB : AB → T) (typeC : AC → T)
    (hNaturality : ∀ b a, typeC (compose b a) = typeB a)
    (a₀ a₁ : AB)
    (hDifferent : typeB a₀ ≠ typeB a₁) :
    ¬ (∀ χ : AC → Bool, ∃ b : BC,
        ∀ a a' : AB, χ (compose b a) = χ (compose b a')) := by
  intro hArrow
  obtain ⟨χ, hSeparate⟩ :=
    exists_persistent_profile_colouring compose typeB typeC
      hNaturality a₀ a₁ hDifferent
  obtain ⟨b, hMono⟩ := hArrow χ
  exact hSeparate b (hMono a₀ a₁)

end CoherentPort
end StructuralRamsey.Girth
