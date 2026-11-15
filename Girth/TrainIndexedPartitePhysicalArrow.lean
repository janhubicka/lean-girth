import Girth.TrainRecursiveRigidPartiteArrow
import Girth.TrainRecursiveCoarsenedSelectedIndexedBundle

set_option autoImplicit false
set_option Elab.async false

/-!
# Selected indexed partite arrow -> genuine PHYSICAL A-edge arrow

The existing selected lower ForestTailStage and its DesignatedArrow
give an INDEXED partite family arrow after coarsening. The finite
picture step of the current old stage instead asks for a PHYSICAL
A-edge-colouring arrow on a local relational A-target. Do not
postulate that stronger arrow independently.

For rigid irreducible A and an actual A-partite target, EVERY
relational A-copy is a partite embedding of the transversal A:
the source-to-part projection is a self-embedding of A, hence the
identity. The existing checked lemma
relationalA_embedding_to_partite_of_rigid constructs it.

Colour each partite A-copy of the core by its literal physical A-edge
carrier. The indexed partite Ramsey arrow selects a genuine gluing
index and makes all source physical A-edges monochromatic. The
partite family index is preserved unchanged.

This is the exact arrow interface required by the new nontrivial
same-vector F_t attachment after the A-part relabelling; connecting
the corresponding actual induced/relabelled structures is a
separate type-transport step.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w

/-- An INDEXED partite A-family arrow provides an indexed PHYSICAL
A-edge arrow, provided every relational A-embedding of the target
preserves its A-parts. No colour multiplication and no selected
index quotient are required. -/
theorem indexedPhysicalArrow_of_partiteFamilyArrow_for_rigidA
    {L : RelLanguage.{u}} {UA X Y I : Type v}
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA X)
    (E : StructuralRamsey.Partite.System L UA Y)
    (f : I → StructuralRamsey.Partite.Embedding Target E)
    (hA : A.Irreducible)
    (hTarget : Target.IsPartiteOver A)
    (hRigid : ∀ a : Embedding A A, a = Embedding.id A)
    (κ : Type w)
    (hIndexed :
      ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) E → κ,
        ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A) Target,
          χ ((f i).comp a) = χ ((f i).comp b)) :
    ∀ χ : OldACarrierEdge A E.toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A Target.toRelStructure,
        χ (actualEdge ((f i).toEmbedding.comp a)) =
          χ (actualEdge ((f i).toEmbedding.comp b)) := by
  intro χ
  obtain ⟨i, hMono⟩ :=
    hIndexed (fun g => χ (actualEdge g.toEmbedding))
  refine ⟨i, ?_⟩
  intro a b
  let aa := relationalA_embedding_to_partite_of_rigid
    A Target hA hTarget hRigid a
  let bb := relationalA_embedding_to_partite_of_rigid
    A Target hA hTarget hRigid b
  have h := hMono aa bb
  change χ (actualEdge (((f i).comp aa).toEmbedding)) =
      χ (actualEdge (((f i).comp bb).toEmbedding)) at h
  exact h

/-- The actual finite ORDERED source A has the rigid irreducible
property automatically, so the checked selected indexed lower
partite arrow is already strong enough for the physical F_t
edge-colouring condition. -/
theorem indexedPhysicalArrow_of_partiteFamilyArrow_for_orderedA
    {L : RelLanguage.{u}} {UA X Y I : Type v}
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA]
    (Target : StructuralRamsey.Partite.System L.withOrder UA X)
    (E : StructuralRamsey.Partite.System L.withOrder UA Y)
    (f : I → StructuralRamsey.Partite.Embedding Target E)
    (hTarget : Target.IsPartiteOver A₀.ordered)
    (κ : Type w)
    (hIndexed :
      ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A₀.ordered) E → κ,
        ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered) Target,
          χ ((f i).comp a) = χ ((f i).comp b)) :
    ∀ χ : OldACarrierEdge A₀.ordered E.toRelStructure → κ,
      ∃ i : I, ∀ a b : Embedding A₀.ordered Target.toRelStructure,
        χ (actualEdge ((f i).toEmbedding.comp a)) =
          χ (actualEdge ((f i).toEmbedding.comp b)) := by
  exact indexedPhysicalArrow_of_partiteFamilyArrow_for_rigidA
    A₀.ordered Target E f
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
    hTarget (fun e => orderedA_self_embedding_is_id A₀ e)
    κ hIndexed

end StructuralRamsey.Girth
