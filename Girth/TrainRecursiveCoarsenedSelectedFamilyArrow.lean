import Girth.TrainRecursiveCoarsenedRamseyArrow
import Girth.TrainRecursiveLargeBaseCoarsening

set_option autoImplicit false
set_option Elab.async false

/-!
# Preserve the literal selected gluing index in the coarsened Ramsey arrow

The existing partiteArrow_after_coarsen_of_designatedRelationalArrow proves
a genuine partite Ramsey arrow. Its exported Partite.Arrow conclusion,
however, forgets which SELECTED lower-stage copy provided that arrow.

The nontrivial refiningPictureStep_of_fineWitness needs more: for every
partite A-colouring, it must choose an index from the ACTUAL subtype of
selected designated B-copies, and show that the corresponding prescribed
coarsened partite embedding is monochromatic.

The same verified relational-arrow-to-partite-arrow argument proves this
strictly stronger indexed conclusion. It extends a partite colouring to
all relational A-embeddings with an arbitrary default on nonpartite
embeddings, then retains the precise selected label returned by the
relational DesignatedArrow. No arbitrary new copy, image-carrier quotient,
Hales--Jewett-power girth or local PictureStep is introduced.

This is a genuinely needed interface to the existing
ForestTailStage.refiningPictureStep_of_fineWitness; the lower selected
stage and its DesignatedArrow are still explicit hypotheses.
Circulation only; no appendix or manuscript validation markers.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {P Q VB X : Type v}

/-- Strengthening of the existing coarsened partite arrow: the witness
is indexed by the LITERAL selected designated-copy subtype, not by an
arbitrary partite embedding of the target in the output. -/
theorem selectedPartiteFamilyArrow_after_coarsen_of_designatedRelationalArrow
    (A : RelStructure L Q)
    (Target : StructuralRamsey.Partite.System L Q VB)
    (D : StructuralRamsey.Partite.System L Q P)
    (E : StructuralRamsey.Partite.System L P X)
    (hE : E.IsPartiteOver D.toRelStructure)
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (selected : Set (DesignatedCopy
      Target.toRelStructure D.toRelStructure E family))
    (κ : Type w) [Nonempty κ]
    (hRelArrow : ∀ χ : Embedding A E.toRelStructure → κ,
      ∃ q : {q : DesignatedCopy
        Target.toRelStructure D.toRelStructure E family // q ∈ selected},
        ∀ a b : Embedding A Target.toRelStructure,
          χ (q.1.embedding.comp a) = χ (q.1.embedding.comp b)) :
    ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A)
        (E.coarsenVia D hE) → κ,
      ∃ i : {q : DesignatedCopy
        Target.toRelStructure D.toRelStructure E family // q ∈ selected},
        ∀ a b : StructuralRamsey.Partite.Embedding
            (StructuralRamsey.Partite.transversal A) Target,
          χ ((selectedPartiteGluingFamily_of_largeBase
            Target D E hE family hFamilyParts selected i).comp a) =
          χ ((selectedPartiteGluingFamily_of_largeBase
            Target D E hE family hFamilyParts selected i).comp b) := by
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
  obtain ⟨q, hMono⟩ := hRelArrow χraw
  let g := selectedPartiteGluingFamily_of_largeBase
    Target D E hE family hFamilyParts selected q
  have hUnderlying (e : StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A) Target) :
      (g.comp e).toEmbedding = q.1.embedding.comp e.toEmbedding := by
    rfl
  refine ⟨q, ?_⟩
  intro e1 e2
  calc
    χ (g.comp e1) = χraw (g.comp e1).toEmbedding :=
      (hRaw (g.comp e1)).symm
    _ = χraw (q.1.embedding.comp e1.toEmbedding) :=
      congrArg χraw (hUnderlying e1)
    _ = χraw (q.1.embedding.comp e2.toEmbedding) :=
      hMono e1.toEmbedding e2.toEmbedding
    _ = χraw (g.comp e2).toEmbedding :=
      congrArg χraw (hUnderlying e2).symm
    _ = χ (g.comp e2) := hRaw (g.comp e2)

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {P Q VB : Type v}

/-- A REAL lower ForestTailStage DesignatedArrow yields the exact
selected-index partite family arrow consumed by the nontrivial
fine-witness PictureStep. It preserves the actual stage.selected label,
unlike the ordinary Partite.Arrow conclusion. -/
theorem ForestTailStage.selectedFamilyArrow_after_largeBaseCoarsen
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
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow S κ) :
    ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A)
        (S.system.coarsenVia D S.isPartite) → κ,
      ∃ i : {q : DesignatedCopy
        Target.toRelStructure D.toRelStructure S.system family //
          q ∈ S.selected},
        ∀ a b : StructuralRamsey.Partite.Embedding
            (StructuralRamsey.Partite.transversal A) Target,
          χ ((selectedPartiteGluingFamily_of_largeBase
            Target D S.system S.isPartite family hFamilyParts S.selected i).comp a) =
          χ ((selectedPartiteGluingFamily_of_largeBase
            Target D S.system S.isPartite family hFamilyParts S.selected i).comp b) := by
  apply selectedPartiteFamilyArrow_after_coarsen_of_designatedRelationalArrow
    A Target D S.system S.isPartite family hFamilyParts
    S.selected κ
  intro χ
  obtain ⟨q, hSelected, hMono⟩ := hArrow χ
  exact ⟨⟨q, hSelected⟩, hMono⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
