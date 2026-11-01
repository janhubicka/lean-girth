import Girth.TrainSelectedPictureRefinementReady
import Girth.ActualActivePartitePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# The recursive local witness on the true active subsystem

Reuse the canonical actualActiveSubsystemPartite on the true active carrier. Its
vertices and relations remain literally unchanged: only the part map is
pulled back along the processed base embedding.  A recursive A-partite
witness can then be relabelled into the old picture.  Its entire core lies
over the processed base copy, and its local partite Ramsey arrow supplies
the projected selection needed by the actual attachment.

The construction never enlarges the active subsystem to all vertices in
the same parts.  It needs no extension of colours to unrelated embeddings
and no nonempty-colour assumption.  The remaining geometric local bounds,
including indexed output supreme-cycle transfer, remain explicit inputs.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- The active system is genuinely A-partite, including reflection on
irreducible substructures, whenever the old picture is partite over D. -/
theorem actualActiveSubsystemPartite_isPartiteOver
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hC : C.IsPartiteOver D) (e : Embedding A D) :
    (actualActiveSubsystemPartite A C e.toFunctionEmbedding).IsPartiteOver A := by
  let inclusion : Embedding
      (actualActiveSubsystemPartite A C e.toFunctionEmbedding).toRelStructure
      (C.restrict e.toFunctionEmbedding).toRelStructure := {
    toFun := fun x => ⟨x.val,
      activeCarrier_subset_support A C e.toFunctionEmbedding x.property⟩
    injective := by
      intro x y h
      exact Subtype.ext (congrArg
        (fun z : C.support e.toFunctionEmbedding => z.val) h)
    map_rel_iff := fun _ _ => Iff.rfl
  }
  exact (StructuralRamsey.Partite.Induced.restrict_isPartiteOver
    D C A hC e).comp inclusion.isHomomorphismEmbedding

/-- A local partite embedding becomes the literal gluing map into the
relabelled core; the underlying relational embedding is unchanged. -/
def activePartiteToRelabelledCore
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) (E : StructuralRamsey.Partite.System L UA Y)
    (f : StructuralRamsey.Partite.Embedding (actualActiveSubsystemPartite A C α) E) :
    StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C α)) (E.relabel α) where
  toEmbedding := f.toEmbedding
  map_part x := (congrArg α (f.map_part x)).trans
    (activeSourcePart_spec A C α x)

/-- Every old projected A-copy is a part-preserving copy in the exact
rebased active subsystem. -/
def activeProjectedPartite
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) (a : StructuralRamsey.Partite.ProjectedEmbedding A C α) :
    StructuralRamsey.Partite.Embedding (StructuralRamsey.Partite.transversal A)
      (actualActiveSubsystemPartite A C α) where
  toEmbedding := (activeInduceProjected A a
    (projected_mem_activeCarrier A C α a)).val
  map_part x := by
    apply α.injective
    exact (activeSourcePart_spec A C α
      ⟨a.val x, projected_mem_activeCarrier A C α a x⟩).trans (a.property x)

/-- A local part-preserving A-copy has the processed projection after
relabeling the core parts. -/
def partiteEmbedding_relabelProjected
    (A : RelStructure L UA) (α : UA ↪ P)
    (E : StructuralRamsey.Partite.System L UA Y)
    (a : StructuralRamsey.Partite.Embedding
      (StructuralRamsey.Partite.transversal A) E) :
    StructuralRamsey.Partite.ProjectedEmbedding A (E.relabel α) α :=
  ⟨a.toEmbedding, fun x => congrArg α (a.map_part x)⟩

/-- The local partite family arrow gives the exact projected selection.
No colours are assigned to embeddings outside the processed projection. -/
theorem activeLocalSelection_of_partiteFamilyArrow
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) (E : StructuralRamsey.Partite.System L UA Y)
    (f : I → StructuralRamsey.Partite.Embedding (actualActiveSubsystemPartite A C α) E)
    (κ : Type w)
    (hArrow : ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) E → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) (actualActiveSubsystemPartite A C α),
        χ ((f i).comp a) = χ ((f i).comp b)) :
    ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A (E.relabel α) α → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.ProjectedEmbedding A C α,
        χ ((activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp
          (activePartiteToRelabelledCore A C α E (f i))) =
        χ ((activeInduceProjected A b (projected_mem_activeCarrier A C α b)).comp
          (activePartiteToRelabelledCore A C α E (f i))) := by
  intro χ
  obtain ⟨i, hi⟩ := hArrow (fun a => χ (partiteEmbedding_relabelProjected A α E a))
  refine ⟨i, ?_⟩
  intro a b
  have route (a : StructuralRamsey.Partite.ProjectedEmbedding A C α) :
      partiteEmbedding_relabelProjected A α E ((f i).comp (activeProjectedPartite A C α a)) =
        (activeInduceProjected A a (projected_mem_activeCarrier A C α a)).comp
          (activePartiteToRelabelledCore A C α E (f i)) := by
    apply Subtype.ext
    apply Embedding.ext
    intro x
    rfl
  rw [← route a, ← route b]
  exact hi (activeProjectedPartite A C α a) (activeProjectedPartite A C α b)

namespace TrainRecursiveWitness

section ActualStep

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)
variable {VB : Type v} {B : RelStructure L.withOrder VB}
variable {D : RelStructure L.withOrder P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (stage : ForestTailStage A₀.ordered B D family t targetTrain allowed)
variable (hBaseLinear : ALinear A₀.ordered D) (e : Embedding A₀.ordered D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A₀.ordered stage.system e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L.withOrder UA Y) [Finite Y] [Finite I]
variable (f : I → StructuralRamsey.Partite.Embedding
  (actualActiveSubsystemPartite A₀.ordered stage.system e.toFunctionEmbedding) E)

local notation "Core" => E.relabel e.toFunctionEmbedding
local notation "F" => fun i : I =>
  activePartiteToRelabelledCore A stage.system e.toFunctionEmbedding E (f i)
variable (U : EdgeTrainLevels (OldACarrierEdge A₀.ordered E.toRelStructure) t.length)
local notation "Rigid" => fun (a : Embedding A D) (h : SameCopy a e) =>
  ordered_embedding_eq_of_sameCopy a e h

/-- An actual A-partite recursive core supplies core support automatically.
Its partite family arrow suffices for the concrete refining picture step,
without a stronger arrow on every relational A-embedding of the core. -/
theorem ForestTailStage.activeAttachment_refiningPictureStep_of_partiteFamilyArrow
    (bounds : ActiveAttachmentBounds stage hA e active (Core) (F) U)
    (ht : 0 < t.length) (remaining : List (UA ↪ P))
    (hFresh : e.toFunctionEmbedding ∉ remaining)
    (hReady : ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1)
      (e.toFunctionEmbedding :: remaining) stage)
    (κ : Type w)
    (hArrow : ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A) E → κ,
      ∃ i : I, ∀ a b : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A)
        (actualActiveSubsystemPartite A stage.system e.toFunctionEmbedding),
        χ ((f i).comp a) = χ ((f i).comp b)) :
    ForestTailStage.FirstRefinementReady ht (t.headD 0 - 1) remaining (stage.activeAttachment_of_local_bounds
      hA hBaseLinear e Rigid active (Core) (F) U bounds) ∧
      PictureStep stage (stage.activeAttachment_of_local_bounds
      hA hBaseLinear e Rigid active (Core) (F) U bounds) e.toFunctionEmbedding κ := by
  refine ⟨stage.activeAttachment_firstRefinementReady A₀ hBaseLinear e active
    (Core) (F) U bounds ?_ ht remaining hFresh hReady, ?_⟩
  · intro y
    exact ⟨E.part y, rfl⟩
  · apply stage.activeAttachment_pictureStep hA hBaseLinear e Rigid active
      (Core) (F) U bounds κ
    exact activeLocalSelection_of_partiteFamilyArrow A stage.system
      e.toFunctionEmbedding E f κ hArrow

end ActualStep
end TrainRecursiveWitness
end StructuralRamsey.Girth
