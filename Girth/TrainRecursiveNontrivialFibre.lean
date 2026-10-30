import Girth.TrainRecursiveReadyConstruction

set_option Elab.async false

/-!
# Recursive passes need local witnesses only on nontrivial physical fibres

The ordered-source identity picture step already handles a projected fibre
whose physical A-copy carriers form a subsingleton.  This module wires that
step into the actual finite pass: a supplied local operator is used only
when two distinct physical projected edges exist.  Empty and singleton
fibres retain the entire selected stage, including its train, forest and
tail conditions.  The concrete refinement-readiness predicate drops the
processed profile by its existing tail law.

The two physical projected edges restrict to two distinct support edges of
the true active induced target.  Thus each requested local witness has the
nontrivial target required by the forest increment; this is derived from
the dispatch condition rather than imposed on skipped fibres.

This proves finite-pass assembly from nontrivial local steps.  It does not
construct those steps or their cycle, forest and remaining-refinability
proofs, and does not assert the full recursive witness theorem.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X : Type v}

/-- Distinct physical projected A-copies give distinct genuine support
edges inside the true active induced target.  No coverage, ordering or
strongness assumption is needed for this restriction. -/
theorem activeSupport_two_distinct_of_projected_carriers
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (a b : StructuralRamsey.Partite.ProjectedEmbedding A C α)
    (hab : copyCarrier a.val ≠ copyCarrier b.val) :
    ∃ e f : OldACarrierEdge A
        (C.toRelStructure.induce (activeCarrier A C α)), e ≠ f := by
  let a' := activeInduceProjected A a (projected_mem_activeCarrier A C α a)
  let b' := activeInduceProjected A b (projected_mem_activeCarrier A C α b)
  refine ⟨actualEdge a'.val, actualEdge b'.val, ?_⟩
  intro heq
  have hcar := congrArg (fun e : OldACarrierEdge A
    (C.toRelStructure.induce (activeCarrier A C α)) => e.1) heq
  change copyCarrier a'.val = copyCarrier b'.val at hcar
  apply hab
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hu : a'.val u ∈ copyCarrier b'.val := by
      rw [← hcar]
      exact ⟨u, rfl⟩
    obtain ⟨z, hz⟩ := hu
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨u, rfl⟩
    have hu : b'.val u ∈ copyCarrier a'.val := by
      rw [hcar]
      exact ⟨u, rfl⟩
    obtain ⟨z, hz⟩ := hu
    exact ⟨z, congrArg Subtype.val hz⟩

section OrderedPass

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)

variable {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {allowed : Fin (t.length + 1) → Set P}

/-- An ordered finite pass needs a genuine local operator only on a fibre
containing two distinct physical projected edges.  The readiness-drop law
is used precisely when the identity transition skips a smaller fibre. -/
theorem ForestTailStage.profileStep_of_nontrivialStep
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    (S : ForestTailStage A B D family t targetTrain allowed)
    (α : UA ↪ P) (remaining : List (UA ↪ P)) (κ : Type w)
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready (α :: remaining) S)
    (hSkipReady : (Set.range (fun a :
      StructuralRamsey.Partite.ProjectedEmbedding A S.system α =>
        copyCarrier a.val)).Subsingleton → Ready remaining S)
    (actualStep : ∀ e : Embedding A D,
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      Ready (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready remaining T ∧ PictureStep S T α κ := by
  classical
  by_cases hPhysical : (Set.range (fun a :
      StructuralRamsey.Partite.ProjectedEmbedding A S.system α =>
        copyCarrier a.val)).Subsingleton
  · exact ⟨S, hSkipReady hPhysical,
      pictureStep_self_of_subsingleton_physical_fibre
        A₀ B D family t targetTrain allowed S α κ hPhysical⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hPhysical
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hPair : ∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system α,
        copyCarrier a.val ≠ copyCarrier b.val := ⟨a, b, hxy⟩
    obtain ⟨e, he⟩ := baseEmbedding_of_projectedEmbedding
      A D S.system hA S.isPartite α a
    subst α
    exact actualStep e hPair hReady

/-- Assemble the selected ordered-source Ramsey witness from its actual
initial stage and operators only for nontrivial physical fibres.  Skipped
fibres use the identity stage and the supplied readiness-drop law. -/
theorem constructFromInitial_of_nontrivialSteps
    [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P) [Finite P]
    (family : Set (Embedding B D)) [Nonempty family]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hInitialTail : ∀ j : Fin t.length, 0 < j.val →
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
          targetTrain (List.length_pos_iff.mpr ht.nonempty))
        j.castSucc).FullSystemGirthGT (t.get j))
    (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B, χ (b.comp a₁) = χ (b.comp a₂))
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready (projectionProfileList UA P)
      (initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hInitialTail))
    (skipReady : ∀ (α : UA ↪ P) (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      Ready (α :: remaining) S →
      (Set.range (fun a : StructuralRamsey.Partite.ProjectedEmbedding A S.system α =>
        copyCarrier a.val)).Subsingleton → Ready remaining S)
    (actualStep : ∀ (e : Embedding A D) (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      Ready (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready [] T ∧ DesignatedArrow T κ := by
  let initial := initialForestTailStage_of_tail A hA B D family t ht
    targetTrain allowed hSupportNonempty hSupportCovers hGirth
    hTargetParameters hInitialTail
  have hLift : ∀ b : Embedding B D, b ∈ family →
      ∃ q : DesignatedCopy B D initial.system family,
        q ∈ initial.selected ∧ q.base = b := by
    intro b hb
    exact initialPicture_lifts B D family b hb
  apply ForestTailStage.ramseyPass initial (projectionProfileList UA P) κ
    Ready hReady mem_projectionProfileList hBase hLift
  intro α remaining S hReadyS
  exact ForestTailStage.profileStep_of_nontrivialStep A₀ S α remaining κ
    Ready hReadyS (skipReady α remaining S hReadyS)
    (fun e hPair hReadyE => actualStep e remaining S hPair hReadyE)

/-- Natural target data and a concrete refinement invariant reduce the
local construction to fibres with two distinct physical projected edges.
Initial readiness and readiness of every skipped fibre are proved; no
operator, new witness or auxiliary readiness premise is needed there. -/
theorem constructFromTargetCuts_of_nontrivialRefiningSteps
    [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (D : RelStructure L.withOrder P) [Finite P]
    (family : Set (Embedding B D))
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j))
    (refinementBudget : ℕ) (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B, χ (b.comp a₁) = χ (b.comp a₂))
    (actualStep : ∀ (e : Embedding A D) (remaining : List (UA ↪ P))
      (S : ForestTailStage A B D family t targetTrain allowed),
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
        refinementBudget (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
            refinementBudget remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      DesignatedArrow T κ := by
  let : Nonempty family := by
    obtain ⟨b, hb⟩ := baseFamily_nonempty_of_arrow A B D family κ hBase
    exact ⟨⟨b, hb⟩⟩
  let ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop :=
    ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
      refinementBudget
  have hTail := initialTail_of_targetCuts A hA B D family t ht targetTrain
    hSupportNonempty hGirth hTargetCuts
  have hReady : ready (projectionProfileList UA P)
      (initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hTail) :=
    initialForestTailStage_firstRefinementReady A hA B D family t ht
      targetTrain allowed hSupportNonempty hSupportCovers hGirth
      hTargetParameters hTail refinementBudget (projectionProfileList UA P)
  obtain ⟨T, _, hArrow⟩ := constructFromInitial_of_nontrivialSteps A₀ B D family
    t ht targetTrain allowed hSupportNonempty hSupportCovers hGirth
    hTargetParameters hTail κ hBase ready hReady
    (fun _ _ _ h _ => ForestTailStage.FirstRefinementReady.tail h) actualStep
  exact ⟨T, hArrow⟩

end OrderedPass

end StructuralRamsey.Girth.TrainRecursiveWitness
