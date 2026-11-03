import Girth.TrainFillingInheritedTrain

set_option Elab.async false

/-!
# Recover the exact wagon embedding from a faithful physical edge map

An actual selected M-copy has an injective physical edge map into N.
At a proper train cut, source and target wagon labels are equality
classes of physical edges. If the edge map preserves AND REFLECTS
parent equality, then the map on wagon labels exists uniquely and is
injective, without assuming a wagon embedding in advance.

The only coverage premise is surjectivity of the SOURCE edge-to-wagon
parent map. It holds automatically for genuine quotient wagon labels.
There is NO surjectivity requirement on the target wagon map: unused
ambient wagons have no effect on the selected copy.

This abstracts another exact-realization field from the global Track C
parentwise scattering input. Proving faithful source/target wagon
relations for the actual selected N-copy remains the next application.
-/

namespace StructuralRamsey.Girth

universe v

/-- Data available from a genuine train embedding on physical edges,
when parent names denote actual wagons rather than an arbitrary set of
unused names. No output wagon embedding or its injectivity is supplied. -/
structure FaithfulPhysicalWagonMap (E F P Q : Type v) where
  localParent : E → P
  ambientParent : F → Q
  edge : E ↪ F
  local_surjective : Function.Surjective localParent
  parent_iff : ∀ e f : E,
    localParent e = localParent f ↔
      ambientParent (edge e) = ambientParent (edge f)

namespace FaithfulPhysicalWagonMap

variable {E F P Q : Type v} (R : FaithfulPhysicalWagonMap E F P Q)

noncomputable def sourceRepresentative (p : P) : E :=
  Classical.choose (R.local_surjective p)

theorem sourceRepresentative_parent (p : P) :
    R.localParent (R.sourceRepresentative p) = p :=
  Classical.choose_spec (R.local_surjective p)

/-- Every genuine source wagon maps to the ambient wagon of any one of
its physical edges. Parent equality reflection makes the map injective. -/
noncomputable def wagonEmbedding : P ↪ Q where
  toFun p := R.ambientParent (R.edge (R.sourceRepresentative p))
  inj' := by
    intro p q hpq
    have hLocal : R.localParent (R.sourceRepresentative p) =
        R.localParent (R.sourceRepresentative q) :=
      (R.parent_iff (R.sourceRepresentative p)
        (R.sourceRepresentative q)).mpr hpq
    rw [R.sourceRepresentative_parent p,
      R.sourceRepresentative_parent q] at hLocal
    exact hLocal

/-- The wagon embedding commutes LITERALLY with the source and target
physical-edge parent maps, including in the empty-source case. -/
theorem wagonEmbedding_parent (e : E) :
    R.wagonEmbedding (R.localParent e) = R.ambientParent (R.edge e) := by
  change R.ambientParent (R.edge
    (R.sourceRepresentative (R.localParent e))) =
      R.ambientParent (R.edge e)
  apply (R.parent_iff
    (R.sourceRepresentative (R.localParent e)) e).mp
  exact R.sourceRepresentative_parent (R.localParent e)

/-- No fake target wagon is introduced. The image of the reconstructed
wagon embedding is exactly the set of ambient wagons touched by source
physical edges. Full surjectivity onto all ambient wagons is not needed. -/
theorem wagonEmbedding_range :
    Set.range R.wagonEmbedding =
      Set.range (fun e : E => R.ambientParent (R.edge e)) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨R.sourceRepresentative p, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨R.localParent e, R.wagonEmbedding_parent e⟩

end FaithfulPhysicalWagonMap
end StructuralRamsey.Girth
