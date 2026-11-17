import Girth.PortSideP4Patterns

/-!
# From closed-port graph geometry to the three P4 birth types

This supplies the geometric hypotheses of PortSideP4Patterns:
* the physical side classifier is total because L ∪ R = univ;
* free gluing prevents left-private/right-private adjacency;
* midpoint closure prevents the pattern shared-private-shared.

Consequently an induced P4 that meets both private sides has one of
three geometric birth shapes. The proof uses only a simple four-vertex
path (with distinct vertices two apart), so inducedness is not needed
for this occurrence-classification step. This does NOT assert a Ramsey
arrow or preservation of the higher E-copy-system girth.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {adj : W → W → Prop}
variable {L R : Set W}

/-- Classify a vertex relative to two subsets. A cover assumption is
used later to ensure right means right-private, not outside both. -/
noncomputable def sideLocation (L R : Set W) (x : W) : PortSide := by
  classical
  exact if x ∈ L then (if x ∈ R then .shared else .left) else .right

theorem sideLocation_left_iff (x : W) :
    sideLocation L R x = .left ↔ x ∈ L \ R := by
  classical
  by_cases hL : x ∈ L <;> by_cases hR : x ∈ R <;>
    simp [sideLocation, hL, hR, Set.mem_diff]

theorem sideLocation_shared_iff (x : W) :
    sideLocation L R x = .shared ↔ x ∈ L ∩ R := by
  classical
  by_cases hL : x ∈ L <;> by_cases hR : x ∈ R <;>
    simp [sideLocation, hL, hR, Set.mem_inter_iff]

theorem sideLocation_right_iff
    (hCover : L ∪ R = Set.univ) (x : W) :
    sideLocation L R x = .right ↔ x ∈ R \ L := by
  classical
  have hxCover : x ∈ L ∨ x ∈ R := by
    have h : x ∈ L ∪ R := by rw [hCover]; exact Set.mem_univ x
    exact h
  by_cases hL : x ∈ L
  · by_cases hR : x ∈ R <;>
      simp [sideLocation, hL, hR, Set.mem_diff]
  · have hR : x ∈ R := hxCover.resolve_left hL
    simp [sideLocation, hL, hR, Set.mem_diff]

/-- A finite truth-table lemma: the allowed-adjacency predicate means
exactly the absence of both forbidden private-side pairs. -/
theorem sideStepAllowed_iff (a b : PortSide) :
    SideStepAllowed a b ↔
      ¬(a = .left ∧ b = .right) ∧
      ¬(a = .right ∧ b = .left) := by
  cases a <;> cases b <;> decide

theorem sideLocation_step_of_free_adj
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    {x y : W} (hxy : adj x y) :
    SideStepAllowed (sideLocation L R x) (sideLocation L R y) := by
  apply (sideStepAllowed_iff _ _).2
  constructor
  · rintro ⟨hx, hy⟩
    exact hNoCross ((sideLocation_left_iff (L := L) (R := R) x).1 hx)
      ((sideLocation_right_iff (L := L) (R := R) hCover y).1 hy) hxy
  · rintro ⟨hx, hy⟩
    exact hNoCross ((sideLocation_left_iff (L := L) (R := R) y).1 hy)
      ((sideLocation_right_iff (L := L) (R := R) hCover x).1 hx)
      (hSymm hxy)

/-- On a simple path, a shared-private-shared triple is impossible at
a midpoint-closed interface. -/
theorem sideLocation_no_hidden_midpoint
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c : W}
    (hacNe : a ≠ c) (hab : adj a b) (hbc : adj b c) :
    NoHiddenPrivateMidpoint
      (sideLocation L R a)
      (sideLocation L R b)
      (sideLocation L R c) := by
  intro ha hc
  have haPort : a ∈ L ∩ R :=
    (sideLocation_shared_iff (L := L) (R := R) a).1 ha
  have hcPort : c ∈ L ∩ R :=
    (sideLocation_shared_iff (L := L) (R := R) c).1 hc
  have hbPort : b ∈ L ∩ R :=
    hPortClosed haPort hcPort hacNe hab (hSymm hbc)
  exact (sideLocation_shared_iff (L := L) (R := R) b).2 hbPort

/-- Exact location types for a crossing four-vertex path. If the two
original sides and the common interface are midpoint-closed, the
interface hypothesis follows by SupportedPartialClosureEquiv
(in the graph-midpoint specialization). -/
theorem crossing_P4_birth_shape_of_closed_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {a b c d : W}
    (hacNe : a ≠ c) (hbdNe : b ≠ d)
    (hab : adj a b) (hbc : adj b c) (hcd : adj c d)
    (hCross : CrossesPrivateSides
      (sideLocation L R a) (sideLocation L R b)
      (sideLocation L R c) (sideLocation L R d)) :
    IsCrossPortP4Birth
      (sideLocation L R a) (sideLocation L R b)
      (sideLocation L R c) (sideLocation L R d) := by
  exact only_three_cross_port_P4_types _ _ _ _
    hCross
    (sideLocation_step_of_free_adj hCover hNoCross hSymm hab)
    (sideLocation_step_of_free_adj hCover hNoCross hSymm hbc)
    (sideLocation_step_of_free_adj hCover hNoCross hSymm hcd)
    (sideLocation_no_hidden_midpoint hSymm hPortClosed hacNe hab hbc)
    (sideLocation_no_hidden_midpoint hSymm hPortClosed hbdNe hbc hcd)

end CoherentPort
end StructuralRamsey.Girth
