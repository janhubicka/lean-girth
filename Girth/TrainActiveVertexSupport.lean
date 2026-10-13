import Girth.TrainActualActiveSharedEdge

/-!
# Every active gluing vertex has a genuine shared support edge

The nonempty active-fibre theorem supplies *some* shared A-edge.
For the top-parent bridge we need the sharper pointwise fact:
EVERY vertex of the true active carrier lies on a genuine old
A-support edge all of whose vertices are in that active carrier.

This follows immediately from the definition of activeCarrier
as the union of projected A-copy carriers. The assertion can fail
for an arbitrary gluing set with isolated vertices; we do not
replace the true active carrier by a larger support-part union.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA P X : Type v}

/-- The real active gluing subsystem has no isolated A-support
vertices: every one is incident with a genuinely shared old edge,
not merely a member of the ambient support parts. -/
theorem activeCarrier_vertex_has_sharedOldAEdge
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P)
    (x : X) (hx : x ∈ activeCarrier A C α) :
    ∃ T : SharedOldACarrierEdge A C.toRelStructure
        (activeCarrier A C α), x ∈ T.1.1 := by
  rcases hx with ⟨e, ⟨a, rfl⟩⟩
  let T : OldACarrierEdge A C.toRelStructure :=
    ⟨copyCarrier e.val, ⟨e.val, rfl⟩⟩
  have hT : T.1 ⊆ activeCarrier A C α := by
    intro y hy
    change y ∈ copyCarrier e.val at hy
    rcases hy with ⟨b, rfl⟩
    exact projected_mem_activeCarrier A C α e b
  refine ⟨⟨T, hT⟩, ?_⟩
  exact ⟨a, rfl⟩

end StructuralRamsey.Girth
