import Girth.TrainFillingPrivateUniform
import Girth.TrainFillingIndexedChoiceCore

set_option Elab.async false

/-!
# Actual relational choices supply the heterogeneous private family

The ordered coloured Ramsey input supplies a collection of strong relational
embeddings W* of W into the common X. Each embedding may select different
positions and different support edges. The already verified
UniformPrivateTemplate.ofStrongEmbedding turns each one into the exact
PrivateWagonInput used by the indexed G0 assembly.

This is a CONSTRUCTOR from relational embeddings, not an assumption that the
desired private geometry holds. The remaining arrow-existence theorem must
still choose the common X and the correct collection of embeddings and carry
the selected target through contraction/filling.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA W X V P C : Type v}

/-- Convert every selected strong relational W* inside X into its own local
private extension, using a fixed ordered identification of first wagons
with W. There is no uniformity assumption on the images of different
choices. -/
noncomputable def relationalPrivateChoices
    (A : RelStructure L UA) (B : RelStructure L W)
    (R : RelStructure L X)
    (choice : C → RelStructure.Embedding B R)
    (hStrong : ∀ c : C, AStrong A R (copyCarrier (choice c)))
    (hCovered : ∀ x : W,
      ∃ a : RelStructure.Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W) :
    C → PrivateWagonInput V P X :=
  fun c =>
    (UniformPrivateTemplate.ofStrongEmbedding A B R
      (choice c) (hStrong c) hCovered).toPrivateWagonInput oldCarrier identify

/-- At every chosen W* the physical selected edge set is exactly the
support-edge image of that particular strong embedding. In particular the
sets are allowed to differ with the choice. -/
theorem relationalPrivateChoices_selectedEdges
    (A : RelStructure L UA) (B : RelStructure L W)
    (R : RelStructure L X)
    (choice : C → RelStructure.Embedding B R)
    (hStrong : ∀ c : C, AStrong A R (copyCarrier (choice c)))
    (hCovered : ∀ x : W,
      ∃ a : RelStructure.Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    (c : C) (p : P) :
    (relationalPrivateChoices A B R choice hStrong hCovered oldCarrier identify c).selectedEdges p =
      (UniformPrivateTemplate.ofStrongEmbedding A B R
        (choice c) (hStrong c) hCovered).selectedEdges := rfl

/-- The existing private-geometry theorem is available choicewise with no
new strongness, coverage or output-system-girth hypotheses. -/
noncomputable def relationalPrivateChoiceGeometry
    (A : RelStructure L UA) (B : RelStructure L W)
    (R : RelStructure L X)
    (choice : C → RelStructure.Embedding B R)
    (hStrong : ∀ c : C, AStrong A R (copyCarrier (choice c)))
    (hCovered : ∀ x : W,
      ∃ a : RelStructure.Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ W)
    {Q : Type v} (parent : P → Q) (c : C) :
    OrderOneData.ComponentTargetGeometry
      ((relationalPrivateChoices A B R choice hStrong hCovered
        oldCarrier identify c).data parent) PUnit.unit :=
  PrivateWagonInput.componentGeometry
    (relationalPrivateChoices A B R choice hStrong hCovered
      oldCarrier identify c) parent

end StructuralRamsey.Girth
