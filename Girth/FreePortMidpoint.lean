import Girth.TypedInterfaceForest

/-!
# Midpoint completion over a free vertex port

For a graph regarded only through its adjacency relation, free gluing
along left ∩ right creates no cross-side edges. The common neighbour
of a left-private and a right-private vertex is forced into that port.

When the port has at most one vertex, each old side also remains closed
against NEW midpoint values on pairs of its old vertices. This is true
even though NEW midpoint relations between opposite private sides may
appear; such relations can create newly coloured P3 and P4 copies.

The statements below are abstract adjacency lemmas. They do not
assert graph girth, uniqueness of a midpoint, or any Ramsey arrow.
Uniqueness follows separately from the no-four-cycle hypothesis.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v}
variable {adj : W → W → Prop}
variable {L R : Set W}

/-- If two private-side vertices have a common neighbour after free
gluing, that neighbour lies in the interface. -/
theorem cross_common_neighbour_mem_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    {x y z : W}
    (hx : x ∈ L \ R) (hy : y ∈ R \ L)
    (hxz : adj x z) (hyz : adj y z) :
    z ∈ L ∩ R := by
  have hzCover : z ∈ L ∨ z ∈ R := by
    have h : z ∈ L ∪ R := by
      rw [hCover]
      exact Set.mem_univ z
    exact h
  constructor
  · by_contra hzNotL
    rcases hzCover with hzL | hzR
    · exact hzNotL hzL
    · exact hNoCross hx ⟨hzR, hzNotL⟩ hxz
  · by_contra hzNotR
    rcases hzCover with hzL | hzR
    · exact hNoCross ⟨hzL, hzNotR⟩ hy (hSymm hyz)
    · exact hzNotR hzR

/-- The graph's pairwise-neighbour relation is complete on cross-side
inputs using only the port data. This is the exact extra domain of the
partial midpoint function created by the free union. -/
theorem cross_common_neighbour_iff_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    {x y z : W}
    (hx : x ∈ L \ R) (hy : y ∈ R \ L) :
    (adj x z ∧ adj y z) ↔
      (z ∈ L ∩ R ∧ adj x z ∧ adj y z) := by
  constructor
  · intro h
    exact ⟨cross_common_neighbour_mem_port hCover hNoCross hSymm hx hy h.1 h.2,
      h.1, h.2⟩
  · intro h
    exact ⟨h.2.1, h.2.2⟩

/-- When the interface is subsingleton, no new common neighbour of
a pair of distinct LEFT vertices can lie outside the left side.
This is the closure-reflection statement needed by a midpoint
completion built over one glued vertex. -/
theorem left_midpoint_values_remain_internal
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSmall : (L ∩ R).Subsingleton)
    {x y z : W}
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y)
    (hxz : adj x z) (hyz : adj y z) :
    z ∈ L := by
  by_contra hzNotL
  have hzR : z ∈ R := by
    have h : z ∈ L ∪ R := by
      rw [hCover]
      exact Set.mem_univ z
    rcases h with hzL | hzR
    · exact False.elim (hzNotL hzL)
    · exact hzR
  have hzPrivate : z ∈ R \ L := ⟨hzR, hzNotL⟩
  have hxR : x ∈ R := by
    by_contra hxNotR
    exact hNoCross ⟨hx, hxNotR⟩ hzPrivate hxz
  have hyR : y ∈ R := by
    by_contra hyNotR
    exact hNoCross ⟨hy, hyNotR⟩ hzPrivate hyz
  exact hxy (hSmall ⟨hx, hxR⟩ ⟨hy, hyR⟩)

/-- The symmetric right-side version. -/
theorem right_midpoint_values_remain_internal
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hSmall : (L ∩ R).Subsingleton)
    {x y z : W}
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y)
    (hxz : adj x z) (hyz : adj y z) :
    z ∈ R := by
  have hNoCrossSwap :
      ∀ ⦃a b⦄, a ∈ R \ L → b ∈ L \ R → ¬ adj a b := by
    intro a b ha hb hab
    exact hNoCross hb ha (hSymm hab)
  have hCoverSwap : R ∪ L = Set.univ := by
    simpa only [Set.union_comm] using hCover
  have hSmallSwap : (R ∩ L).Subsingleton := by
    simpa only [Set.inter_comm] using hSmall
  exact left_midpoint_values_remain_internal
    (L := R) (R := L) hCoverSwap hNoCrossSwap hSmallSwap hx hy hxy hxz hyz

end CoherentPort
end StructuralRamsey.Girth
