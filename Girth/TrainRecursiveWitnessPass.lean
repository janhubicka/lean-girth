import Girth.TrainRecursiveWitness
import Girth.TrainSelectedPictureTwoStandard
import Girth.TrainAllAdjacentParameterPreservation
import Girth.ForestMixedSetBound
import Girth.ForestMixedIrreducibleCoverage
import Girth.SupportForestToTree
import PartiteConstruction.Partite.Construction
import PartiteConstruction.Partite.Initial

/-!
# Finite passes with selected copies and the complete train invariant

The recursive operators must return finite witnesses together with their
colouring arrow, selected target copies, bottom mixed forests, and every tail
cycle condition.  Here these use the project's actual relational support
edges and selected-picture incidence model.

A transition is stronger than a bare relational PictureProperty: its
embedding preserves selected labels and preserves AND reflects every train
relation on physical A-edges.  These clauses compose throughout backwards
selection.  In particular the Ramsey arrow never switches to arbitrary
projected B-lifts or loses the target train structure.

The existence of geometric local steps remains an explicit hypothesis.
This module proves the finite iteration and Ramsey extraction once those
steps are provided.  Refinability of unprocessed fibres, where needed to
produce a step, still belongs to its concrete construction; no such
refinability theorem is asserted here.  No ambient support edge is pruned.

To instantiate a nontrivial local `PictureStep`, the geometric construction
must combine the actual physical forest increment with Track A's physical
segmentation and supremeness pullback, Track B's generated-wagon strongness,
linearity and two-standard obstruction, and Track C's all-level parameters
and filling/subcopy cycle transfer.  `TrainRecursiveWitnessInitialStage`
assembles the actual initial stage with an explicit tail-cycle input.
Preservation of remaining-fibre refinability, the cutoff-two tail step and
larger-cutoff refinement forgetting remain explicit construction work.  The
identity step for a fibre with at most one physical edge is proved below.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The physical edge label of an actual A-copy. -/
def actualEdge {X : Type v} {A : RelStructure L UA}
    {C : RelStructure L X} (a : RelStructure.Embedding A C) :
    OldACarrierEdge A C :=
  ⟨copyCarrier a, ⟨a, rfl⟩⟩

/-- Transport one designated copy along a partite embedding, retaining its
literal prescribed base label. -/
def mapDesignated {X Y : Type v} {B : RelStructure L VB}
    {D : RelStructure L P}
    {S : StructuralRamsey.Partite.System L P X}
    {T : StructuralRamsey.Partite.System L P Y}
    {family : Set (RelStructure.Embedding B D)}
    (f : StructuralRamsey.Partite.Embedding S T)
    (q : DesignatedCopy B D S family) : DesignatedCopy B D T family :=
  ⟨q.base, q.base_mem, q.lift.comp f⟩

@[simp] theorem mapDesignated_id {X : Type v} {B : RelStructure L VB}
    {D : RelStructure L P} {S : StructuralRamsey.Partite.System L P X}
    {family : Set (RelStructure.Embedding B D)}
    (q : DesignatedCopy B D S family) :
    mapDesignated (StructuralRamsey.Partite.Embedding.id S) q = q := by
  cases q
  rfl

@[simp] theorem mapDesignated_comp {X Y Z : Type v}
    {B : RelStructure L VB} {D : RelStructure L P}
    {S : StructuralRamsey.Partite.System L P X}
    {T : StructuralRamsey.Partite.System L P Y}
    {R : StructuralRamsey.Partite.System L P Z}
    {family : Set (RelStructure.Embedding B D)}
    (g : StructuralRamsey.Partite.Embedding T R)
    (f : StructuralRamsey.Partite.Embedding S T)
    (q : DesignatedCopy B D S family) :
    mapDesignated (g.comp f) q = mapDesignated g (mapDesignated f q) := rfl

/-- Test every ambient A-edge and precisely the selected B-supports. -/
def testedAB {X : Type v}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (piece : HypergraphPiece X) : Prop :=
  (∃ a : RelStructure.Embedding A C.toRelStructure,
    piece = HypergraphPiece.oneEdge (copyCarrier a)) ∨
  (∃ b : DesignatedCopy B D C family, b ∈ selected ∧
    piece = bSupportPiece A b.embedding)

/-- An actual finite picture with selected target copies and all forest/tail
invariants.  Each selected B-copy is a strong train embedding of the fixed
input target train.  No condition is imposed on unselected projected lifts.
-/
structure ForestTailStage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (family : Set (RelStructure.Embedding B D))
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P) where
  Vertex : Type v
  finiteVertex : Finite Vertex
  system : StructuralRamsey.Partite.System L P Vertex
  isPartite : system.IsPartiteOver D
  aLinear : ALinear A system.toRelStructure
  supportNonempty : Nonempty (OldACarrierEdge A system.toRelStructure)
  supportCovers : ∀ x : Vertex,
    ∃ e : OldACarrierEdge A system.toRelStructure, x ∈ e.1
  selected : Set (DesignatedCopy B D system family)
  selectedPhysicalInjective : Function.Injective
    (fun q : {b : DesignatedCopy B D system family // b ∈ selected} =>
      bSupportPiece A q.1.embedding)
  mixedCoverage : ∀ S : Set Vertex, (system.toRelStructure.induce S).Irreducible →
    (∃ q : DesignatedCopy B D system family, q ∈ selected ∧
      ∀ z : S, ∃ b : VB, z.1 = q.embedding b) ∨
    (∃ a : RelStructure.Embedding A system.toRelStructure,
      ∀ z : S, ∃ u : UA, z.1 = a u)
  strong : ∀ b : DesignatedCopy B D system family, b ∈ selected →
    AStrong A system.toRelStructure (copyCarrier b.embedding)
  train : EdgeTrainLevels (OldACarrierEdge A system.toRelStructure) t.length
  targetRestriction : ∀ b : DesignatedCopy B D system family, b ∈ selected →
    ∀ μ : Fin (t.length + 1), ∀ a₁ a₂ : RelStructure.Embedding A B,
      train.rel μ (actualEdge (b.embedding.comp a₁))
        (actualEdge (b.embedding.comp a₂)) ↔
      targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)
  parameters : train.AdjacentParameters (fun edge => edge.1)
    (fun ν => system.part ⁻¹' allowed ν)
  bottomForest : FiniteMixedForestThrough
    (testedAB A B D system family selected) (t.headD 0)
  tailGirth : ∀ j : Fin t.length, 0 < j.val →
    (selectedPictureOrderOneData A B D system family selected
      train j.castSucc).FullSystemGirthGT (t.get j)

attribute [instance] ForestTailStage.finiteVertex

/-- Order-conversion output retains the forest and the selected target train
copies, and adds full system-girth at every cut. -/
structure OrderStage
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (family : Set (RelStructure.Embedding B D))
    (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    extends ForestTailStage A B D family t targetTrain allowed where
  allCutGirth : ∀ j : Fin t.length,
    (selectedPictureOrderOneData A B D system family selected
      train j.castSucc).FullSystemGirthGT (t.get j)

section Pass

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (RelStructure.Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- A backwards-selection map preserves the selected labels and the entire
train on physical edges.  The selected-copy strongness is carried by the
stage, so it remains available for the final selected Ramsey copy. -/
structure TransitionEmbedding
    (S T : ForestTailStage A B D family t targetTrain allowed) where
  toPartite : StructuralRamsey.Partite.Embedding S.system T.system
  map_selected : ∀ q : DesignatedCopy B D S.system family,
    q ∈ S.selected → mapDesignated toPartite q ∈ T.selected
  train_iff : ∀ μ : Fin (t.length + 1),
    ∀ a₁ a₂ : RelStructure.Embedding A S.system.toRelStructure,
      T.train.rel μ (actualEdge (toPartite.toEmbedding.comp a₁))
        (actualEdge (toPartite.toEmbedding.comp a₂)) ↔
      S.train.rel μ (actualEdge a₁) (actualEdge a₂)

/-- Identity selection leaves the selected family and all train levels fixed. -/
def TransitionEmbedding.id
    (S : ForestTailStage A B D family t targetTrain allowed) :
    TransitionEmbedding S S where
  toPartite := StructuralRamsey.Partite.Embedding.id S.system
  map_selected := by intro q hq; simpa using hq
  train_iff := fun _ _ _ => Iff.rfl

/-- The train-reflection and selected-label clauses compose along the pass. -/
def TransitionEmbedding.comp
    {S T R : ForestTailStage A B D family t targetTrain allowed}
    (g : TransitionEmbedding T R) (f : TransitionEmbedding S T) :
    TransitionEmbedding S R where
  toPartite := g.toPartite.comp f.toPartite
  map_selected := by
    intro q hq
    exact g.map_selected (mapDesignated f.toPartite q) (f.map_selected q hq)
  train_iff := by
    intro μ a₁ a₂
    exact (g.train_iff μ (f.toPartite.toEmbedding.comp a₁)
      (f.toPartite.toEmbedding.comp a₂)).trans (f.train_iff μ a₁ a₂)

/-- Local homogeneous selection with the stronger transition map. -/
def PictureStep
    (S T : ForestTailStage A B D family t targetTrain allowed)
    (α : UA ↪ P) (κ : Type w) : Prop :=
  ∀ χ : StructuralRamsey.Partite.ProjectedEmbedding A T.system α → κ,
    ∃ f : TransitionEmbedding S T,
      ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
        χ (e₁.comp f.toPartite) = χ (e₂.comp f.toPartite)

/-- Forgetting selected labels and train reflection gives the usual property.
The reverse implication is not assumed. -/
theorem PictureStep.pictureProperty
    {S T : ForestTailStage A B D family t targetTrain allowed}
    {α : UA ↪ P} {κ : Type w} (h : PictureStep S T α κ) :
    StructuralRamsey.Partite.PictureProperty A S.system α T.system κ := by
  intro χ
  obtain ⟨f, hf⟩ := h χ
  exact ⟨f.toPartite, hf⟩

/-- Simultaneous fibre homogeneity with selected-copy and train transport. -/
def CanonicalOn
    (S T : ForestTailStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) : Prop :=
  ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
    ∃ f : TransitionEmbedding S T, ∀ α ∈ profiles,
      ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
        χ (f.toPartite.toEmbedding.comp e₁.val) =
          χ (f.toPartite.toEmbedding.comp e₂.val)

/-- Finite iteration with a stage-dependent invariant for the remaining
fibres.  `Ready` can record precisely the unprocessed-fibre refinability
needed by the larger-cutoff step; no arbitrary stage is assumed refinable.
-/
theorem ForestTailStage.finitePass
    (S : ForestTailStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w)
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family t targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready [] T ∧ CanonicalOn S T profiles κ := by
  induction profiles generalizing S with
  | nil =>
      refine ⟨S, hReady, ?_⟩
      intro χ
      exact ⟨TransitionEmbedding.id S, fun α h => (List.not_mem_nil h).elim⟩
  | cons α profiles ih =>
      obtain ⟨R, hReadyR, hStep⟩ := step α profiles S hReady
      obtain ⟨T, hReadyT, hT⟩ := ih R hReadyR
      refine ⟨T, hReadyT, ?_⟩
      intro χ
      obtain ⟨g, hg⟩ := hT χ
      obtain ⟨f, hf⟩ := hStep
        (fun e => χ (g.toPartite.toEmbedding.comp e.val))
      refine ⟨g.comp f, ?_⟩
      intro β hβ e₁ e₂
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact hf e₁ e₂
      · exact hg β hβ (e₁.comp f.toPartite) (e₂.comp f.toPartite)

/-- A covering finite list suffices for simultaneous homogeneity of all
projections.  `Ready` is retained through exactly the processed list.
-/
theorem ForestTailStage.allProjections
    (S : ForestTailStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w)
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family t targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready [] T ∧
      ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
        ∃ f : TransitionEmbedding S T, ∀ α : UA ↪ P,
          ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
            χ (f.toPartite.toEmbedding.comp e₁.val) =
              χ (f.toPartite.toEmbedding.comp e₂.val) := by
  obtain ⟨T, hReadyT, hT⟩ := ForestTailStage.finitePass
    S profiles κ Ready hReady step
  refine ⟨T, hReadyT, ?_⟩
  intro χ
  obtain ⟨f, hf⟩ := hT χ
  exact ⟨f, fun α => hf α (hProfiles α)⟩

/-- The selected Ramsey arrow.  Strongness and the target train-restriction
law of the selected witness are available from the same returned stage. -/
def DesignatedArrow
    (S : ForestTailStage A B D family t targetTrain allowed) (κ : Type w) : Prop :=
  ∀ χ : RelStructure.Embedding A S.system.toRelStructure → κ,
    ∃ b : DesignatedCopy B D S.system family, b ∈ S.selected ∧
      ∀ a₁ a₂ : RelStructure.Embedding A B,
        χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)

theorem DesignatedArrow.arrow
    {S : ForestTailStage A B D family t targetTrain allowed} {κ : Type w}
    (h : DesignatedArrow S κ) :
    StructuralRamsey.Arrow A B S.system.toRelStructure κ := by
  intro χ
  obtain ⟨b, _, hb⟩ := h χ
  exact ⟨b.embedding, hb⟩

/-- The selected monochromatic copy has the required strongness and the
exact original train equivalences, including reflection at every level. -/
theorem DesignatedArrow.strongTrain
    {S : ForestTailStage A B D family t targetTrain allowed} {κ : Type w}
    (h : DesignatedArrow S κ)
    (χ : RelStructure.Embedding A S.system.toRelStructure → κ) :
    ∃ b : DesignatedCopy B D S.system family, b ∈ S.selected ∧
      AStrong A S.system.toRelStructure (copyCarrier b.embedding) ∧
      (∀ μ : Fin (t.length + 1), ∀ a₁ a₂ : RelStructure.Embedding A B,
        S.train.rel μ (actualEdge (b.embedding.comp a₁))
          (actualEdge (b.embedding.comp a₂)) ↔
        targetTrain.rel μ (actualEdge a₁) (actualEdge a₂)) ∧
      (∀ a₁ a₂ : RelStructure.Embedding A B,
        χ (b.embedding.comp a₁) = χ (b.embedding.comp a₂)) := by
  obtain ⟨b, hb, hmono⟩ := h χ
  exact ⟨b, hb, S.strong b hb, S.targetRestriction b hb, hmono⟩

/-- Selected-copy extraction from a fully homogeneous pass, using only the
prescribed base-family arrow and actual selected lifts in the initial stage.
-/
theorem designatedArrow_of_canonicalOn
    (S T : ForestTailStage A B D family t targetTrain allowed)
    (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D S.system family, q ∈ S.selected ∧ q.base = b)
    (hCanon : ∀ χ : RelStructure.Embedding A T.system.toRelStructure → κ,
      ∃ f : TransitionEmbedding S T, ∀ α : UA ↪ P,
        ∀ e₁ e₂ : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
          χ (f.toPartite.toEmbedding.comp e₁.val) =
            χ (f.toPartite.toEmbedding.comp e₂.val)) :
    DesignatedArrow T κ := by
  classical
  intro χ
  obtain ⟨f, hf⟩ := hCanon χ
  let θ : RelStructure.Embedding A D → κ := fun α =>
    if hα : Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system α) then
      χ (f.toPartite.toEmbedding.comp (Classical.choice hα).val)
    else Classical.choice (inferInstance : Nonempty κ)
  have hθ (α : RelStructure.Embedding A D)
      (e : StructuralRamsey.Partite.ProjectedEmbedding A S.system α) :
      θ α = χ (f.toPartite.toEmbedding.comp e.val) := by
    have he : Nonempty
        (StructuralRamsey.Partite.ProjectedEmbedding A S.system α) := ⟨e⟩
    simp only [θ, dite_eq_left he]
    exact hf α.toFunctionEmbedding (Classical.choice he) e
  obtain ⟨b, hb, hmono⟩ := hBase θ
  obtain ⟨q, hq, hqb⟩ := hLift b hb
  subst b
  let projected (a : RelStructure.Embedding A B) :
      StructuralRamsey.Partite.ProjectedEmbedding A S.system (q.base.comp a) :=
    ⟨q.lift.val.comp a, fun x => q.lift.property (a x)⟩
  refine ⟨mapDesignated f.toPartite q, f.map_selected q hq, ?_⟩
  intro a₁ a₂
  have h := hmono a₁ a₂
  rw [hθ (q.base.comp a₁) (projected a₁),
    hθ (q.base.comp a₂) (projected a₂)] at h
  exact h

/-- Conditional finite-pass assembly with a selected strong train Ramsey
arrow and all mixed-forest, parameter and tail invariants on the same output.
The local step consumes the precise remaining-fibre readiness invariant.
-/
theorem ForestTailStage.ramseyPass
    (S : ForestTailStage A B D family t targetTrain allowed)
    (profiles : List (UA ↪ P)) (κ : Type w) [Nonempty κ]
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready profiles S)
    (hProfiles : ∀ α : UA ↪ P, α ∈ profiles)
    (hBase : ∀ χ : RelStructure.Embedding A D → κ,
      ∃ b : RelStructure.Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : RelStructure.Embedding A B,
          χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b : RelStructure.Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D S.system family, q ∈ S.selected ∧ q.base = b)
    (step : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (T : ForestTailStage A B D family t targetTrain allowed),
      Ready (α :: remaining) T →
        ∃ R : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining R ∧ PictureStep T R α κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready [] T ∧ DesignatedArrow T κ := by
  obtain ⟨T, hReadyT, hT⟩ := ForestTailStage.allProjections
    S profiles κ Ready hReady hProfiles step
  exact ⟨T, hReadyT, designatedArrow_of_canonicalOn S T κ hBase hLift hT⟩

end Pass

/-- Empty and one-physical-edge fibres need no attachment.  Ordered-source
rigidity makes their projected embeddings equal, and the identity transition
retains the selected family, the entire train, forests and tail conditions.
-/
theorem pictureStep_self_of_subsingleton_physical_fibre
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
    (B : RelStructure L.withOrder VB) (D : RelStructure L.withOrder P)
    (family : Set (RelStructure.Embedding B D)) (t : List ℕ)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (S : ForestTailStage A₀.ordered B D family t targetTrain allowed)
    (α : UA ↪ P) (κ : Type w)
    (hPhysical : (Set.range (fun e :
      StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered S.system α =>
        copyCarrier e.val)).Subsingleton) :
    PictureStep S S α κ := by
  intro χ
  refine ⟨TransitionEmbedding.id S, ?_⟩
  intro e₁ e₂
  have hSame : SameCopy e₁.val e₂.val :=
    hPhysical ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
  have hEq : e₁ = e₂ :=
    Subtype.ext (ordered_embedding_eq_of_sameCopy e₁.val e₂.val hSame)
  rw [hEq]

/-- The literal designated copy in the disjoint initial picture. -/
def initialDesignatedCopy
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (RelStructure.Embedding B D)) (b : family) :
    DesignatedCopy B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun β : family => β.1.toFunctionEmbedding)) family :=
  ⟨b.1, b.2, ⟨StructuralRamsey.Partite.Initial.copyEmbedding B
    (fun β : family => β.1.toFunctionEmbedding) b, fun _ => rfl⟩⟩

/-- Initial extraction uses exactly the literal disjoint target copies. -/
theorem initialPicture_lifts
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (RelStructure.Embedding B D))
    (b : RelStructure.Embedding B D) (hb : b ∈ family) :
    ∃ q : DesignatedCopy B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun β : family => β.1.toFunctionEmbedding)) family,
      q ∈ Set.range (initialDesignatedCopy B D family) ∧ q.base = b := by
  exact ⟨initialDesignatedCopy B D family ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
