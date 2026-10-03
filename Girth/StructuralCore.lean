import Girth.SupportedTree
import PartiteConstruction.Iterated.SparseningTheorem

/-! # Checked structural core imported from the partite construction

The girth manuscript uses a stronger local forest invariant, but its structural
skeleton is already available in `partite-construction`: Ramsey arrow,
homomorphism-embedding back to the initial witness, bounded local tree-likeness,
and extension of every irreducible substructure to a copy of the target.

Keeping this wrapper in `lean-girth` fixes the exact dependency boundary.  The
remaining main-theorem work is to strengthen generic `TreeAmalgam` witnesses
to `ASupportedTreeAmalgam` witnesses and then prove the support-girth geometry.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- Structural Ramsey/local-tree core on which the girth-specific argument is
built. -/
theorem localTreeRamseyCore
    (A : RelStructure L UA) (B : RelStructure L VB)
    (G : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hRamsey : StructuralRamsey.Arrow A B G κ)
    (hA : A.HereditarilyIrreducible)
    (hB : B.HereditarilyIrreducible)
    (n : ℕ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      StructuralRamsey.Arrow A B C κ ∧
      ∃ p : Z → P,
        C.IsHomomorphismEmbedding G p ∧
        RelStructure.LocallyTreeLike A B C n ∧
        RelStructure.IrreduciblesExtendTo B C := by
  exact
    StructuralRamsey.Partite.IteratedSparsening.
      sparseningRamsey_hereditarilyIrreducible_all
        A B G κ hRamsey hA hB n

end StructuralRamsey.Girth
