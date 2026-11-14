import Girth.TrainFillingPrivateOriginalTarget
import Girth.TrainFillingIndexedChoiceCore

set_option Elab.async false

/-!
# The literal choice-tagged original target vertex map

The actual heterogeneous contracted M has vertex type
  Sigma (c : Choice), (U c).Vertex.
The original target vertex v in the component of choice c is
  ⟨c, Sum.inl v⟩,
not an untagged vertex v of M. The map is injective even if
the original first wagons share their old vertices inside T,
and two DIFFERENT choices have disjoint vertex images.

The checked private targetCarrier is exactly this vertex map's
range. This bridges the manuscript's τ_s to the actual Lean
representation without asking for any target-copy carrier map
as an independent input.

A faithful original-edge map and all its train relations follow
after identifying original E(T) with the first-wagon local edge
indices of the candidate SummandPrivateTemplate; that last
relational/train identification remains to be assembled.

Candidate source, not kernel checked.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- The actual chosen component inclusion τ_c on ORIGINAL vertices,
including the old/private sum tag and the heterogeneous choice tag. -/
def originalTargetVertexEmbedding (c : C) : V ↪ Vertex U where
  toFun v := tagVertex U c (Sum.inl v)
  inj' := by
    intro v w h
    exact Sum.inl.inj ((tagVertex_injective U c) h)

/-- The verified indexed targetCarrier definition is exactly the
range of τ_c, not a new assumed carrier for a phantom target. -/
theorem targetCarrier_eq_originalVertexRange (c : C) :
    targetCarrier U c = Set.range (originalTargetVertexEmbedding U c) := by
  ext z
  constructor
  · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Sum.inl v, ⟨v, rfl⟩, rfl⟩

/-- Original target vertices in different selected W-choices are
disjoint in M, as opposed to those belonging to different
selected OLD parents j(M) in N which may overlap. -/
theorem originalTargetVertexRange_disjoint
    (c d : C) (hcd : c ≠ d) :
    Disjoint (Set.range (originalTargetVertexEmbedding U c))
      (Set.range (originalTargetVertexEmbedding U d)) := by
  rw [← targetCarrier_eq_originalVertexRange U c,
      ← targetCarrier_eq_originalVertexRange U d]
  exact Set.disjoint_of_subset (targetCarrier_subset_component U c)
    (targetCarrier_subset_component U d)
    (componentCarrier_disjoint U c d hcd)

end StructuralRamsey.Girth.IndexedPrivateChoice
