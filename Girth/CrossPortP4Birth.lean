import Girth.FreePortMidpointClosed

/-!
# Exact P4 birth geometry at a singleton free-amalgamation interface

Let a-b-c-d be a path, with a in the left-private part and d in
the right-private part of a free graph union. Then either b or c is
in the shared interface. If the port is subsingleton and b != c,
precisely one internal vertex belongs to the port, and the other
is private on its respective side.

This proves the *shape* of newly born P4 copies: an edge on one side,
a P3 on the other. It is valid even without inducedness or girth
assumptions. It does not assert that the newly born P4 is closed
or provides any Ramsey homogenization.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {adj : W → W → Prop}
variable {L R : Set W}

private theorem next_from_left_private_is_left
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    {a b : W} (ha : a ∈ L \ R) (hab : adj a b) : b ∈ L := by
  by_contra hbNotL
  have hbR : b ∈ R := by
    have h : b ∈ L ∪ R := by rw [hCover]; exact Set.mem_univ b
    rcases h with hL | hR
    · exact False.elim (hbNotL hL)
    · exact hR
  exact hNoCross ha ⟨hbR, hbNotL⟩ hab

private theorem prior_to_right_private_is_right
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    {a b : W} (hb : b ∈ R \ L) (hab : adj a b) : a ∈ R := by
  by_contra haNotR
  have haL : a ∈ L := by
    have h : a ∈ L ∪ R := by rw [hCover]; exact Set.mem_univ a
    rcases h with hL | hR
    · exact hL
    · exact False.elim (haNotR hR)
  exact hNoCross ⟨haL, haNotR⟩ hb hab

/-- Every path of length three crossing a free union through its
private ends must visit the interface at an internal vertex. -/
theorem crossing_path3_internal_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    {a b c d : W}
    (ha : a ∈ L \ R) (hd : d ∈ R \ L)
    (hab : adj a b) (hbc : adj b c) (hcd : adj c d) :
    b ∈ L ∩ R ∨ c ∈ L ∩ R := by
  have hbL : b ∈ L :=
    next_from_left_private_is_left hCover hNoCross ha hab
  have hcR : c ∈ R :=
    prior_to_right_private_is_right hCover hNoCross hd hcd
  by_cases hbR : b ∈ R
  · exact Or.inl ⟨hbL, hbR⟩
  · right
    have hcL : c ∈ L := by
      by_contra hcNotL
      exact hNoCross ⟨hbL, hbR⟩ ⟨hcR, hcNotL⟩ hbc
    exact ⟨hcL, hcR⟩

/-- If the free interface is a singleton (or empty), precisely one
of the two internal path vertices is its shared vertex. The
remaining internal vertex lies in the appropriate private side.
The path cannot exist when the interface is empty. -/
theorem crossing_path3_singleton_port_shape
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSmall : (L ∩ R).Subsingleton)
    {a b c d : W} (hbcNe : b ≠ c)
    (ha : a ∈ L \ R) (hd : d ∈ R \ L)
    (hab : adj a b) (hbc : adj b c) (hcd : adj c d) :
    (b ∈ L ∩ R ∧ c ∈ R \ L) ∨
      (c ∈ L ∩ R ∧ b ∈ L \ R) := by
  have hbL : b ∈ L :=
    next_from_left_private_is_left hCover hNoCross ha hab
  have hcR : c ∈ R :=
    prior_to_right_private_is_right hCover hNoCross hd hcd
  rcases crossing_path3_internal_port hCover hNoCross ha hd hab hbc hcd
    with hbPort | hcPort
  · left
    refine ⟨hbPort, ⟨hcR, ?_⟩⟩
    intro hcL
    exact hbcNe (hSmall hbPort ⟨hcL, hcR⟩)
  · right
    refine ⟨hcPort, ⟨hbL, ?_⟩⟩
    intro hbR
    exact hbcNe (hSmall ⟨hbL, hbR⟩ hcPort)

end CoherentPort
end StructuralRamsey.Girth
