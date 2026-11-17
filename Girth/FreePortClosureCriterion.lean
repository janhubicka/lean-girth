import Girth.PortAttachmentUnique

/-!
# Exact closure test for arbitrary coloured occurrences at a free port

A P4 crossing a closed port is automatically closed in girth-five
graphs; a P5 need not be. The right general criterion is not a
list of location patterns alone:

A vertex subset X of a free union of two graphs over a
midpoint-closed port is closed if and only if
(1) X restricted to each old side is closed INSIDE that side, and
(2) X contains every port vertex adjacent to an X-vertex private
    to each of the opposite sides.

By the unique-port-address lemma, condition (2) is the equality-
of-nonempty-attachment-address test. No girth beyond the closed
port hypothesis is needed in the logical equivalence.

This is a geometric closure theorem, not a Ramsey arrow. The
result can be applied to a proposed coloured A occurrence before
it is added to the canonical closed-copy incidence sort.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v}
variable {adj : W → W → Prop}
variable {L R : Set W}

/-- Closure relative to an ambient side: midpoint outputs restricted
to that side remain in the proposed subset. -/
def MidpointClosedInside
    (adj : W → W → Prop) (ambient S : Set W) : Prop :=
  ∀ ⦃x y z : W⦄,
    x ∈ S → y ∈ S → x ≠ y →
    z ∈ ambient → adj x z → adj y z → z ∈ S

/-- Necessary and sufficient *local* criterion for closing a vertex
set in a free amalgam over a midpoint-closed interface. No size or
finiteness restriction on the port is imposed. -/
theorem midpointClosed_iff_sidewise_and_crossPort
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    (X : Set W) :
    MidpointClosed (adj := adj) X ↔
      (MidpointClosedInside adj L (X ∩ L) ∧
       MidpointClosedInside adj R (X ∩ R) ∧
       ∀ ⦃x y s : W⦄,
         x ∈ X ∩ (L \ R) →
         y ∈ X ∩ (R \ L) →
         s ∈ L ∩ R → adj x s → adj y s → s ∈ X) := by
  constructor
  · intro hClosed
    refine ⟨?_, ?_, ?_⟩
    · intro x y z hx hy hxy hzL hxz hyz
      exact ⟨hClosed hx.1 hy.1 hxy hxz hyz, hzL⟩
    · intro x y z hx hy hxy hzR hxz hyz
      exact ⟨hClosed hx.1 hy.1 hxy hxz hyz, hzR⟩
    · intro x y s hx hy _ hxs hys
      have hxy : x ≠ y := by
        intro h
        apply hy.2.2
        rw [← h]
        exact hx.2.1
      exact hClosed hx.1 hy.1 hxy hxs hys
  · rintro ⟨hLeft, hRight, hCrossPort⟩
    intro x y z hx hy hxy hxz hyz
    have hLeftCase (hxL : x ∈ L) (hyL : y ∈ L) : z ∈ X := by
      have hzL : z ∈ L :=
        old_left_midpoints_remain_inside_of_closed_port
          hCover hNoCross hPortClosed hxL hyL hxy hxz hyz
      exact (hLeft ⟨hx, hxL⟩ ⟨hy, hyL⟩ hxy hzL hxz hyz).1
    have hRightCase (hxR : x ∈ R) (hyR : y ∈ R) : z ∈ X := by
      have hzR : z ∈ R :=
        old_right_midpoints_remain_inside_of_closed_port
          hCover hNoCross hSymm hPortClosed hxR hyR hxy hxz hyz
      exact (hRight ⟨hx, hxR⟩ ⟨hy, hyR⟩ hxy hzR hxz hyz).1
    by_cases hxL : x ∈ L
    · by_cases hyL : y ∈ L
      · exact hLeftCase hxL hyL
      · have hyR : y ∈ R := by
          have h : y ∈ L ∪ R := by
            rw [hCover]
            exact Set.mem_univ y
          exact h.resolve_left hyL
        by_cases hxR : x ∈ R
        · exact hRightCase hxR hyR
        · have hzPort : z ∈ L ∩ R :=
            cross_common_neighbour_mem_port
              hCover hNoCross hSymm
              ⟨hxL, hxR⟩ ⟨hyR, hyL⟩ hxz hyz
          exact hCrossPort
            ⟨hx, ⟨hxL, hxR⟩⟩ ⟨hy, ⟨hyR, hyL⟩⟩
            hzPort hxz hyz
    · have hxR : x ∈ R := by
        have h : x ∈ L ∪ R := by
          rw [hCover]
          exact Set.mem_univ x
        exact h.resolve_left hxL
      by_cases hyR : y ∈ R
      · exact hRightCase hxR hyR
      · have hyL : y ∈ L := by
          have h : y ∈ L ∪ R := by
            rw [hCover]
            exact Set.mem_univ y
          exact h.resolve_right hyR
        have hzPort : z ∈ L ∩ R :=
          cross_common_neighbour_mem_port
            hCover hNoCross hSymm
            ⟨hyL, hyR⟩ ⟨hxR, hxL⟩ hyz hxz
        exact hCrossPort
          ⟨hy, ⟨hyL, hyR⟩⟩ ⟨hx, ⟨hxR, hxL⟩⟩
          hzPort hyz hxz

end CoherentPort
end StructuralRamsey.Girth
