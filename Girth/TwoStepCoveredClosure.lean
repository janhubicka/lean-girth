import Girth.CanonicalClosedOccurrences

/-!
# Closed copies from two-step internal coverage

For graphs of ordinary girth at least five, distinct adjacent
vertices do not have a common neighbour (no triangles), and
distinct vertices do not have two different common neighbours
(no four-cycles).

Consequently any vertex set S in which every two distinct
vertices are adjacent or have a common neighbour INSIDE S
is midpoint-closed. This applies to induced copies of any
diameter-at-most-two graph, including P3, stars and C5.

This is a positive extension criterion for coloured configurations:
automatic midpoint closure becomes an intrinsic property of A,
independent of attachment history and port choices. The theorem
does not produce a Ramsey arrow, high E-copy girth or a global
successor-tree replay map.
-/

namespace StructuralRamsey.Girth
namespace CoherentPort

universe v
variable {W U V : Type v}

/-- For every two distinct vertices of S, there is a graph edge
between them or a length-two path entirely inside S. -/
def TwoStepCovered
    (adj : W → W → Prop) (S : Set W) : Prop :=
  ∀ (x y : W), x ∈ S → y ∈ S → x ≠ y →
    adj x y ∨ ∃ w : W, w ∈ S ∧ adj x w ∧ adj y w

/-- The absence of triangles stated in the form needed to rule
out a common neighbour of two adjacent distinct vertices. -/
def NoTriangleCommonNeighbours
    (adj : W → W → Prop) : Prop :=
  ∀ ⦃x y z : W⦄,
    x ≠ y → adj x y → adj x z → adj y z → False

/-- A girth-five graph has at most one common neighbour of any
two distinct vertices. This excludes four-cycles. -/
def UniqueCommonNeighbours
    (adj : W → W → Prop) : Prop :=
  ∀ ⦃x y z w : W⦄,
    x ≠ y →
    adj x z → adj y z → adj x w → adj y w → z = w

/-- A two-step-covered vertex set is automatically midpoint-closed
under the two elementary ordinary-girth-five conditions. -/
theorem midpointClosed_of_twoStepCovered
    {adj : W → W → Prop} {S : Set W}
    (hTwoStep : TwoStepCovered adj S)
    (hNoTriangles : NoTriangleCommonNeighbours adj)
    (hUnique : UniqueCommonNeighbours adj) :
    MidpointClosed (adj := adj) S := by
  intro x y z hx hy hxy hxz hyz
  rcases hTwoStep x y hx hy hxy with hxyAdj | ⟨w, hw, hxw, hyw⟩
  · exact False.elim (hNoTriangles hxy hxyAdj hxz hyz)
  · have heq : z = w := hUnique hxy hxz hyz hxw hyw
    simpa [heq] using hw

/-- Two-step coverage transfers along an injective induced embedding:
all witnesses in the source become witnesses in the target image. -/
theorem twoStepCovered_range_of_induced
    (A : SimpleGraph U) (G : SimpleGraph V)
    (f : U ↪ V)
    (hInduced : ∀ u v : U,
       G.Adj (f u) (f v) ↔ A.Adj u v)
    (hTwoStep : TwoStepCovered A.Adj Set.univ) :
    TwoStepCovered G.Adj (Set.range f) := by
  intro x y hx hy hxy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have huv : u ≠ v := by
    intro h
    apply hxy
    exact congrArg f h
  rcases hTwoStep u v (Set.mem_univ _) (Set.mem_univ _) huv with
      huvAdj | ⟨w, _, huw, hvw⟩
  · exact Or.inl ((hInduced u v).mpr huvAdj)
  · exact Or.inr
      ⟨f w, ⟨w, rfl⟩, (hInduced u w).mpr huw,
        (hInduced v w).mpr hvw⟩

/-- Every induced embedding of a two-step-covered coloured graph
into a girth-five graph is AUTOMATICALLY midpoint-closed.
The construction is canonical and requires no extra
chosen closure witnesses. -/
def closedGraphEmbedding_of_twoStepCovered
    (A : SimpleGraph U) (G : SimpleGraph V)
    (f : U ↪ V)
    (hInduced : ∀ u v : U,
      G.Adj (f u) (f v) ↔ A.Adj u v)
    (hTwoStep : TwoStepCovered A.Adj Set.univ)
    (hNoTriangles : NoTriangleCommonNeighbours G.Adj)
    (hUnique : UniqueCommonNeighbours G.Adj) :
    ClosedGraphEmbedding A G where
  toEmbedding := f
  induced := hInduced
  closed := midpointClosed_of_twoStepCovered
    (twoStepCovered_range_of_induced A G f hInduced hTwoStep)
    hNoTriangles hUnique

end CoherentPort
end StructuralRamsey.Girth
