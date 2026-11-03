import Girth.TrainRecursiveActivePartite
import PartiteConstruction.Partite.Induced

set_option autoImplicit false

/-!
# Recover a relational designated arrow from a partite arrow for rigid A

The large-base induced partite Ramsey input colours only actual
partite embeddings of A. A lower ForestTailStage's DesignatedArrow,
however, asks for monochromaticity on ALL relational embeddings of
A into the selected target.

This difference disappears when A is irreducible and RIGID, and the
target's part projection is a homomorphism-embedding to A. For every
relational A-embedding a into B, the image a[A] is irreducible.
The projection B.part restricts there to a relational self-embedding
of A. Rigidity forces it to be the identity, so a is already a
genuine partite embedding of transversal A into B.

The partite Ramsey arrow can therefore be restricted to the selected
target, where it gives monochromaticity for ALL relational A-copies
as required by the forest-tail stage's designated arrow.

This is the exact missing source-rigidity interface between #783's
induced power base and #774's larger-base partite arrow. Rigidity is
explicit; this module does NOT silently infer it for an unordered A.
The ordered-A specialization and full recursive witness are separate
obligations. No appendix or final theorem claim.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {Q V X : Type v}

/-- In a rigid irreducible A, every relational copy into a genuinely
A-partite system is automatically part-preserving. The proof uses
reflection on the irreducible WHOLE range, not just relation
preservation by the projection. -/
theorem relationalA_embedding_preserves_parts_of_rigid
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hA : A.Irreducible)
    (hB : B.IsPartiteOver A)
    (hRigid : ∀ e : Embedding A A, e = Embedding.id A)
    (a : Embedding A B.toRelStructure) :
    ∀ x : Q, B.part (a x) = x := by
  let S : Set V := Set.range a
  have hSIrr : (B.toRelStructure.induce S).Irreducible :=
    hA.range_embedding a
  obtain ⟨e, he⟩ := hB.2 S hSIrr
  let aS : Embedding A (B.toRelStructure.induce S) := {
    toFun := fun x => ⟨a x, ⟨x, rfl⟩⟩
    injective := by
      intro x y hxy
      exact a.injective (congrArg Subtype.val hxy)
    map_rel_iff := by
      intro R xs
      exact a.map_rel_iff R xs
  }
  have hSelf : e.comp aS = Embedding.id A := hRigid (e.comp aS)
  intro x
  calc
    B.part (a x) = e (aS x) := (he (aS x)).symm
    _ = (e.comp aS) x := rfl
    _ = x := by rw [hSelf]; rfl

/-- The actual A-partite copy corresponding to a relational copy of A.
There is no arbitrary choice of part labels, and the underlying
relational embedding is preserved exactly. -/
def relationalA_embedding_to_partite_of_rigid
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (hA : A.Irreducible)
    (hB : B.IsPartiteOver A)
    (hRigid : ∀ e : Embedding A A, e = Embedding.id A)
    (a : Embedding A B.toRelStructure) :
    StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A) B where
  toEmbedding := a
  map_part := relationalA_embedding_preserves_parts_of_rigid
    A B hA hB hRigid a

/-- For a rigid irreducible source, the induced partite arrow provides
the desired selected-target monochromaticity on ALL RELATIONAL
A-embeddings of the target, not merely the partite ones. -/
theorem relationalArrow_of_partiteArrow_for_rigidA
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q V)
    (D : StructuralRamsey.Partite.System L Q X)
    (hA : A.Irreducible)
    (hB : B.IsPartiteOver A)
    (hRigid : ∀ e : Embedding A A, e = Embedding.id A)
    (κ : Type w)
    (hArrow : StructuralRamsey.Partite.Arrow
      (StructuralRamsey.Partite.transversal A) B D κ) :
    ∀ χ : Embedding A D.toRelStructure → κ,
      ∃ b : StructuralRamsey.Partite.Embedding B D,
        ∀ a₁ a₂ : Embedding A B.toRelStructure,
          χ (b.toEmbedding.comp a₁) = χ (b.toEmbedding.comp a₂) := by
  intro χ
  obtain ⟨b, hb⟩ := hArrow (fun e => χ e.toEmbedding)
  refine ⟨b, ?_⟩
  intro a₁ a₂
  let e₁ := relationalA_embedding_to_partite_of_rigid
    A B hA hB hRigid a₁
  let e₂ := relationalA_embedding_to_partite_of_rigid
    A B hA hB hRigid a₂
  exact hb e₁ e₂

end StructuralRamsey.Girth
