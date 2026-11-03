import Girth.TrainRecursiveLargeBaseCoarsening
import Girth.TrainRecursiveWitnessPass
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Full selected relational Ramsey arrows survive part-coarsening

The larger-base repair of the nontrivial-fibre recursion needs not only
PARTITE embeddings of the active target in the coarsened lower witness,
but also the correct PARTITE Ramsey arrow.  A lower forest-tail witness
supplies a stronger arrow: it colours ALL relational A-copies and selects
a genuine designated target copy in which those colours are constant.

A colouring of A-partite embeddings into the coarsened witness can be
extended to all relational A-embeddings, using an arbitrary default
colour on embeddings that do not respect the coarsened A-part map.
The lower relational arrow selects a target, whose base embedding is
assumed to respect the larger Q-partite base's parts.  The selected
target is then a genuine partite embedding by the coarsening lemma,
and the stronger monochromaticity restricts to all its partite A-copies.

No raw output arrow or hidden colour extension is an assumption.
The lower genuine forest-tail stage and its selected family do remain
inputs.  This is a conditional interface, not existence of the full
recursive witness, its train certificates or tail SupremeCycleBound.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {P Q VB X : Type v}

/-- Lift the actual designated-copy RELATIONAL arrow over a LARGE Q-partite
base D to a genuine Q-partite arrow after coarsening the witness.
The designated full-target labels are unchanged, and no assumption that
the target part map itself is injective is made. -/
theorem partiteArrow_after_coarsen_of_designatedRelationalArrow
    (A : RelStructure L Q)
    (Target : StructuralRamsey.Partite.System L Q VB)
    (D : StructuralRamsey.Partite.System L Q P)
    (E : StructuralRamsey.Partite.System L P X)
    (hE : E.IsPartiteOver D.toRelStructure)
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (selected : Set (DesignatedCopy Target.toRelStructure D.toRelStructure E family))
    (κ : Type w) [Nonempty κ]
    (hRelArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ q : {q : DesignatedCopy Target.toRelStructure D.toRelStructure E family //
        q ∈ selected},
        ∀ a b : Embedding A Target.toRelStructure,
          χ (q.1.embedding.comp a) = χ (q.1.embedding.comp b)) :
    StructuralRamsey.Partite.Arrow
      (StructuralRamsey.Partite.transversal A)
      Target (E.coarsenVia D hE) κ := by
  classical
  let Coarse := E.coarsenVia D hE
  let admissible (a : Embedding A E.toRelStructure) : Prop :=
    ∀ x : Q, D.part (E.part (a x)) = x
  let lift (a : Embedding A E.toRelStructure)
      (ha : admissible a) :
      StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) Coarse := {
      toEmbedding := a
      map_part := by
        intro x
        exact ha x
    }
  let defaultColour : κ := Classical.choice ‹Nonempty κ›
  intro χ
  let χraw : Embedding A E.toRelStructure → κ := fun a =>
    if ha : admissible a then χ (lift a ha) else defaultColour
  have hRaw (g : StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A) Coarse) :
      χraw g.toEmbedding = χ g := by
    have hg : admissible g.toEmbedding := by
      intro x
      exact g.map_part x
    dsimp [χraw]
    rw [dif_pos hg]
    apply congrArg χ
    exact StructuralRamsey.Partite.Embedding.ext (fun x => rfl)
  obtain ⟨q, hMono⟩ := hRelArrow χraw
  let g := selectedPartiteGluingFamily_of_largeBase
    Target D E hE family hFamilyParts selected q
  refine ⟨g, ?_⟩
  intro e1 e2
  calc
    χ (g.comp e1) = χraw (q.1.embedding.comp e1.toEmbedding) := by
      simpa only [] using (hRaw (g.comp e1)).symm
    _ = χraw (q.1.embedding.comp e2.toEmbedding) :=
      hMono e1.toEmbedding e2.toEmbedding
    _ = χ (g.comp e2) := by
      simpa only [] using hRaw (g.comp e2)

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {P Q VB : Type v}

/-- The actual ForestTailStage designated arrow (colours ALL relational
A-copies) yields the partite family-arrow needed for the next active
fibre, after coarsening a lower witness over a suitably LARGE base. -/
theorem ForestTailStage.partiteArrow_after_largeBaseCoarsen
    (A : RelStructure L Q)
    (Target : StructuralRamsey.Partite.System L Q VB)
    (D : StructuralRamsey.Partite.System L Q P)
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A Target.toRelStructure) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A Target.toRelStructure D.toRelStructure
      family t targetTrain allowed)
    (κ : Type w) [Nonempty κ] (hArrow : DesignatedArrow S κ) :
    StructuralRamsey.Partite.Arrow
      (StructuralRamsey.Partite.transversal A) Target
      (S.system.coarsenVia D S.isPartite) κ := by
  apply partiteArrow_after_coarsen_of_designatedRelationalArrow
    A Target D S.system S.isPartite family hFamilyParts S.selected κ
  intro χ
  obtain ⟨q, hSelected, hMono⟩ := hArrow χ
  exact ⟨⟨q, hSelected⟩, hMono⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
