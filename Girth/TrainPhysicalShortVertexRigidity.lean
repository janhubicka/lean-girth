import Girth.TrainSimultaneousSupreme
import Girth.TrainCyclicOwnerAbsorption

/-!
# Rigidity of short replacement of an edge across two vertex contacts

When a physical edge-labelled source occurrence has two distinct
VERTEX boundary connectors, that source edge is incident with both.
Any short replacement from a supreme standard also meets both.
In a linear pretrain two different physical edges cannot contain two
distinct vertices, so the replacement edge must be the ORIGINAL edge.

This reduces the vertex-vertex physical-edge case of positive-cut
transfer to changing owner provenance, not changing the actual
cycle word. It does not claim the new owner is adjacent or that
minimum cuts strictly decrease. For mixed vertex/wagon boundaries
the two-vertex argument does not apply. Circulation only.
-/

namespace StructuralRamsey.Girth.OrderOneData

universe v
variable {V E I P : Type v} (D : OrderOneData V E I P)

/-- Linearity determines an actual support edge from two distinct
vertices of its carrier. -/
theorem edge_eq_of_two_shared_vertices
    (hLinear : D.LinearPretrain)
    (old fresh : E) (x y : V)
    (hxy : x ≠ y)
    (hOldX : x ∈ D.edgeCarrier old)
    (hOldY : y ∈ D.edgeCarrier old)
    (hFreshX : x ∈ D.edgeCarrier fresh)
    (hFreshY : y ∈ D.edgeCarrier fresh) :
    old = fresh := by
  by_contra hDifferent
  have hSmall := hLinear.1 old fresh hDifferent
  have hAtX : x ∈ D.edgeCarrier old ∩ D.edgeCarrier fresh :=
    ⟨hOldX, hFreshX⟩
  have hAtY : y ∈ D.edgeCarrier old ∩ D.edgeCarrier fresh :=
    ⟨hOldY, hFreshY⟩
  exact hxy (hSmall hAtX hAtY)

/-- Under source physical-edge labelling and two vertex connectors,
a genuine ShortValid replacement is necessarily the same physical
edge. Thus only its potential standard owner changes; the labels
and connectors of the original cycle can remain untouched. -/
theorem BigCycle.shortValid_edge_eq_of_vertex_boundaries
    {n : ℕ} (K : D.BigCycle n)
    (hLinear : D.LinearPretrain)
    (j target : Fin n) (old fresh : E) (x y : V)
    (hLabel : K.label j = Sum.inr old)
    (hLeft : K.connector (trainCyclicPred j) = Sum.inl x)
    (hRight : K.connector j = Sum.inl y)
    (hShort : K.ShortValid D target j fresh) :
    old = fresh := by
  have hNePred : trainCyclicPred j ≠ j := by
    intro heq
    have hh := cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two j
    rw [heq] at hh
    exact (cyclicSucc_ne_self_of_two_le K.length_ge_two j) hh
  have hxy : x ≠ y := by
    intro heq
    have hConn : K.connector (trainCyclicPred j) = K.connector j := by
      rw [hLeft, hRight, heq]
    exact hNePred (K.connector_injective hConn)
  have hOldX : x ∈ D.edgeCarrier old := by
    have hInc := K.right_incident (trainCyclicPred j)
    rw [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two j,
      hLabel, hLeft] at hInc
    exact hInc
  have hOldY : y ∈ D.edgeCarrier old := by
    have hInc := K.left_incident j
    rw [hLabel, hRight] at hInc
    exact hInc
  obtain ⟨_, hFreshLeft, hFreshRight⟩ := hShort
  have hFreshX : x ∈ D.edgeCarrier fresh := by
    simpa [hLeft, Incident, carrier] using hFreshLeft
  have hFreshY : y ∈ D.edgeCarrier fresh := by
    simpa [hRight, Incident, carrier] using hFreshRight
  exact edge_eq_of_two_shared_vertices D hLinear
    old fresh x y hxy hOldX hOldY hFreshX hFreshY

end StructuralRamsey.Girth.OrderOneData
