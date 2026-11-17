import Girth.FreePortMidpoint

/-!
# Midpoint-closed ports preserve old closed embeddings

This strengthens the singleton-port lemma in FreePortMidpoint:
a free graph union along ANY midpoint-closed interface creates no
new midpoint value on two old vertices of either side.

The statement concerns adjacency and relative midpoint closure.
It does not claim that the graph union is of girth >= 5; that has
to be proved separately (notably, a disconnected interface can
create cycles). The union can still create NEW cross-side midpoint
tuples, and hence new coloured P3/P4 occurrences.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v}
variable {adj : W → W → Prop}
variable {L R : Set W}

/-- A set contains all common neighbours of pairs of its distinct vertices.
For girth-five graphs this is precisely closure under the partial midpoint
function. -/
def MidpointClosed (S : Set W) : Prop :=
  ∀ ⦃x y z : W⦄, x ∈ S → y ∈ S → x ≠ y →
    adj x z → adj y z → z ∈ S

/-- Closure of the common interface is enough to guarantee that every
pair of distinct OLD left vertices keeps all its midpoint values inside
the old left side after gluing. -/
theorem old_left_midpoints_remain_inside_of_closed_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
    {x y z : W}
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y)
    (hxz : adj x z) (hyz : adj y z) :
    z ∈ L := by
  by_contra hzNotL
  have hzR : z ∈ R := by
    have hz : z ∈ L ∪ R := by
      rw [hCover]
      exact Set.mem_univ z
    rcases hz with hzL | hzR
    · exact False.elim (hzNotL hzL)
    · exact hzR
  have hzPrivate : z ∈ R \ L := ⟨hzR, hzNotL⟩
  have hxR : x ∈ R := by
    by_contra hxNotR
    exact hNoCross ⟨hx, hxNotR⟩ hzPrivate hxz
  have hyR : y ∈ R := by
    by_contra hyNotR
    exact hNoCross ⟨hy, hyNotR⟩ hzPrivate hyz
  have hzPort : z ∈ L ∩ R :=
    hPortClosed ⟨hx, hxR⟩ ⟨hy, hyR⟩ hxy hxz hyz
  exact hzNotL hzPort.1

/-- Right-side version, with symmetry supplied explicitly so the
geometric crossing hypothesis is still oriented left-to-right. -/
theorem old_right_midpoints_remain_inside_of_closed_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hPortClosed : MidpointClosed (adj := adj) (L ∩ R))
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
  have hPortSwap : MidpointClosed (adj := adj) (R ∩ L) := by
    simpa only [Set.inter_comm] using hPortClosed
  exact old_left_midpoints_remain_inside_of_closed_port
    (L := R) (R := L) hCoverSwap hNoCrossSwap hPortSwap
    hx hy hxy hxz hyz

/-- A common port that is midpoint-closed *inside each of its two sides*
remains midpoint-closed in the whole free union. This follows just by
covering its vertices, with no cycle or Ramsey argument. -/
theorem midpointClosed_port_of_sidewise_closure
    (hCover : L ∪ R = Set.univ)
    (hLeft : ∀ ⦃x y z : W⦄,
      x ∈ L ∩ R → y ∈ L ∩ R → x ≠ y →
      z ∈ L → adj x z → adj y z → z ∈ L ∩ R)
    (hRight : ∀ ⦃x y z : W⦄,
      x ∈ L ∩ R → y ∈ L ∩ R → x ≠ y →
      z ∈ R → adj x z → adj y z → z ∈ L ∩ R) :
    MidpointClosed (adj := adj) (L ∩ R) := by
  intro x y z hx hy hxy hxz hyz
  have hz : z ∈ L ∪ R := by
    rw [hCover]
    exact Set.mem_univ z
  rcases hz with hzL | hzR
  · exact hLeft hx hy hxy hzL hxz hyz
  · exact hRight hx hy hxy hzR hxz hyz

/-- The prior singleton-port case is the degenerate closed-port case.
No separate midpoint argument is required when the port is subsingleton. -/
theorem midpointClosed_of_subsingleton
    (hSmall : (L ∩ R).Subsingleton) :
    MidpointClosed (adj := adj) (L ∩ R) := by
  intro x y z hx hy hxy _ _
  exact False.elim (hxy (hSmall hx hy))

end CoherentPort
end StructuralRamsey.Girth
