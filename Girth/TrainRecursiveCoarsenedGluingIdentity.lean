import Girth.TrainRecursiveActualCoarsenedFullSystem

set_option autoImplicit false
set_option Elab.async false

/-!
# Literal identity of the coarsened selected gluing incidence record

Part coarsening changes only the part function of the selected lower
picture. It neither changes the relational reduct nor creates, deletes,
or merges physical A-support edges. The selected designated-copy subtype
is the ACTUAL gluing index type and the constructed partite gluing map
has the same underlying relational embedding. Consequently the entire
OrderOneData structure, at every cut (including bottom and universal top),
is definitionally the original selected gluing structure.

We check this stronger identity separately from any FullSystemGirthGT
certificate. No girth, fresh local step, or selected output theorem is
added as an assumption. The part-preserving lower family condition remains.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}
variable (A : RelStructure L UA)
variable (Old : StructuralRamsey.Partite.System L P X)
variable (α : UA ↪ P)
variable (D : StructuralRamsey.Partite.System L UA V)

variable {family : Set (Embedding (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A (Old.toRelStructure.induce (activeCarrier A Old α))) t.length}
variable {allowed : Fin (t.length + 1) → Set V}
variable (S : ForestTailStage A (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure family t targetTrain allowed)
variable (hFamilyParts : ∀ b, b ∈ family →
  ∀ x : activeCarrier A Old α,
    D.part (b x) = activeSourcePart A Old α x)

include hFamilyParts

/-- The actual constructed partite gluing copy is not a surrogate copy:
its underlying relational embedding is *literally* the selected original
copy. This identity includes every vertex, not only its image carrier. -/
theorem ForestTailStage.coarsenedSelected_gluingEmbedding_eq
    (i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
      b ∈ S.selected}) :
    (selectedPartiteGluingFamily_of_largeBase
      (actualActiveSubsystemPartite A Old α) D S.system S.isPartite family hFamilyParts
      S.selected i).toEmbedding = i.1.embedding := rfl

/-- Stronger than the positive girth transfer: the COMPLETE selected
physical incidence records are identical at every cut, including the
old equality cut and universal top. There is no quotient of physical
edge occurrences, support pruning, or change in wagon names. -/
theorem ForestTailStage.coarsenedSelected_gluingData_eq
    (ν : Fin (t.length + 1)) :
    activeGluingWitnessOrderOneData A Old α
      (S.system.coarsenVia D S.isPartite).toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          (actualActiveSubsystemPartite A Old α) D S.system S.isPartite family hFamilyParts
          S.selected i).toEmbedding)
      S.train ν =
    activeGluingWitnessOrderOneData A Old α
      S.system.toRelStructure
      (fun i : {b : DesignatedCopy (Old.toRelStructure.induce (activeCarrier A Old α)) D.toRelStructure S.system family //
          b ∈ S.selected} => i.1.embedding)
      S.train ν := rfl

end StructuralRamsey.Girth.TrainRecursiveWitness
