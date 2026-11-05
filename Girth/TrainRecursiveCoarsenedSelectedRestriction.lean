import Girth.TrainRecursiveCoarsenedRamseyArrow

set_option autoImplicit false
set_option Elab.async false

/-!
# Exact selected train restriction after large-base part coarsening

There is no reason to specialize the fine-train restriction bridge to
the literal true active subsystem. The genuine lower ForestTailStage
already stores the entire source train restriction on every SELECTED
target label. Coarsening only the base parts leaves its underlying
relational embedding literally unchanged.

This generic statement works for every genuine A-partite target and
larger A-partite base, under the actual part-preservation hypothesis
for the selected base labels. In particular it applies to the exact
true active source without adding any gluing-family equivalence,
pruning physical edges, or replacing selected labels by carriers.

The theorem does NOT assert existence of the lower stage, an
appropriately refined target train, or attached output cycle bounds.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

variable (A : RelStructure L UA)
variable (Target : StructuralRamsey.Partite.System L UA VB)
variable (D : StructuralRamsey.Partite.System L UA P)
variable {family : Set (Embedding Target.toRelStructure D.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A Target.toRelStructure) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (S : ForestTailStage A Target.toRelStructure D.toRelStructure
  family t targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
  D.part (b x) = Target.part x)

/-- Every selected partite gluing copy reflects AND preserves the
actual lower target train at every fine coordinate. No quotient of
labels or ambient edge deletion is used. -/
theorem ForestTailStage.coarsenedSelected_trainRestriction
    (ν : Fin (t.length + 1))
    (i : {b : DesignatedCopy Target.toRelStructure D.toRelStructure
      S.system family // b ∈ S.selected})
    (a b : Embedding A Target.toRelStructure) :
    S.train.rel ν
      (actualEdge
        ((selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite
          family hFamilyParts S.selected i).toEmbedding.comp a))
      (actualEdge
        ((selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite
          family hFamilyParts S.selected i).toEmbedding.comp b)) ↔
    targetTrain.rel ν (actualEdge a) (actualEdge b) := by
  change S.train.rel ν
      (actualEdge (i.1.embedding.comp a))
      (actualEdge (i.1.embedding.comp b)) ↔
    targetTrain.rel ν (actualEdge a) (actualEdge b)
  exact S.targetRestriction i.1 i.2 ν a b

end StructuralRamsey.Girth.TrainRecursiveWitness
