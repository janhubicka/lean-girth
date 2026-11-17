import Girth.CrossPortP4Endpoint

/-!
# A closed graph port has unique attachment addresses

If an interface S is closed under the midpoint operation, no
outside vertex can have two distinct neighbours in S: such a
vertex would be a midpoint of those two port vertices and closure
would force it into S.

Thus each private vertex has a canonical, set-valued *port address*:
the subset of interface vertices adjacent to it, which is empty or
a singleton. Two vertices on opposite private sides admit a common
neighbour exactly when their port addresses intersect, and in that
case the common neighbour is unique. This is the exact new mixed
midpoint geometry; no arbitrary owner choice is required.

These statements are independent of any global graph-girth bound.
They are NOT an unrestricted Ramsey theorem and do not preserve
higher labelled E-copy-system girth automatically.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W : Type v} {adj : W → W → Prop}
variable {L R S : Set W}

/-- The attachment address of x at S, without choosing a value. -/
def PortNeighbours (adj : W → W → Prop) (S : Set W) (x : W) : Set W :=
  {s | s ∈ S ∧ adj x s}

/-- A midpoint-closed port meets the neighbour set of every outside
vertex in at most one point. -/
theorem portNeighbours_subsingleton_of_midpointClosed
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hClosed : MidpointClosed (adj := adj) S)
    {x : W} (hx : x ∉ S) :
    (PortNeighbours adj S x).Subsingleton := by
  intro s hs t ht
  by_contra hne
  have hxInS : x ∈ S :=
    hClosed hs.1 ht.1 hne (hSymm hs.2) (hSymm ht.2)
  exact hx hxInS

/-- The new midpoint between opposite private sides is UNIQUE,
without invoking ordinary graph girth: port closure is enough. -/
theorem cross_private_midpoint_unique_of_closed_port
    (hCover : L ∪ R = Set.univ)
    (hNoCross : ∀ ⦃a b⦄, a ∈ L \ R → b ∈ R \ L → ¬ adj a b)
    (hSymm : ∀ ⦃a b⦄, adj a b → adj b a)
    (hClosed : MidpointClosed (adj := adj) (L ∩ R))
    {x y z w : W}
    (hx : x ∈ L \ R) (hy : y ∈ R \ L)
    (hxz : adj x z) (hyz : adj y z)
    (hxw : adj x w) (hyw : adj y w) : z = w := by
  have hxOutside : x ∉ L ∩ R := by
    intro h
    exact hx.2 h.2
  have hOne := portNeighbours_subsingleton_of_midpointClosed
    hSymm hClosed hxOutside
  have hzPort : z ∈ L ∩ R :=
    cross_common_neighbour_mem_port hCover hNoCross hSymm
      hx hy hxz hyz
  have hwPort : w ∈ L ∩ R :=
    cross_common_neighbour_mem_port hCover hNoCross hSymm
      hx hy hxw hyw
  exact hOne ⟨hzPort, hxz⟩ ⟨hwPort, hxw⟩

end CoherentPort
end StructuralRamsey.Girth
