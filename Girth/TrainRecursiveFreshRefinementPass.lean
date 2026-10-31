import Girth.TrainRecursiveNontrivialFibre

set_option Elab.async false
set_option autoImplicit false

/-!
# Fresh profiles in the refinement-ready finite pass

The profile enumeration has no repetitions.  Tracking that fact together
with readiness gives each nontrivial local operator the precise freshness
hypothesis used by untouched-fibre preservation: its processed profile is
absent from the remaining tail.  The local refinement theorem therefore
preserves readiness on precisely the still-unprocessed fibres.

The Ramsey conclusion, actual finite stages and literal selected-family
arrow are unchanged.  Initial readiness and skipped-fibre transitions
remain constructed.  Existence of the fresh nontrivial local operator is
still explicit; this module does not construct a recursive local witness.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}

section OrderedPass

variable (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA]
local notation "A" => A₀.ordered
local notation "hA" => RelStructure.HereditarilyIrreducible.irreducible
  (RelStructure.ordered_hereditarilyIrreducible A₀)

/-- The repetition-free profile pass requests a nontrivial local step
only when its processed profile is absent from the remaining tail.
Nodup is maintained internally alongside the supplied readiness predicate. -/
theorem constructFromInitial_of_freshNontrivialSteps
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
      e.toFunctionEmbedding ∉ remaining →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding, copyCarrier a.val ≠ copyCarrier b.val) →
      Ready (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready [] T ∧ DesignatedArrow T κ := by
  let freshReady : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop :=
    fun profiles S => profiles.Nodup ∧ Ready profiles S
  have hFreshReady : freshReady (projectionProfileList UA P)
      (initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hInitialTail) :=
    ⟨projectionProfileList_nodup, hReady⟩
  obtain ⟨T, hReadyT, hArrow⟩ := constructFromInitial_of_nontrivialSteps
    A₀ B D family t ht targetTrain allowed hSupportNonempty hSupportCovers
    hGirth hTargetParameters hInitialTail κ hBase freshReady hFreshReady
    (fun α remaining S h hPhysical =>
      ⟨(List.nodup_cons.mp h.1).2, skipReady α remaining S h.2 hPhysical⟩)
    (fun e remaining S hPair h => by
      have hFresh : e.toFunctionEmbedding ∉ remaining := (List.nodup_cons.mp h.1).1
      obtain ⟨T, hReadyT, hStep⟩ := actualStep e remaining S hFresh hPair h.2
      exact ⟨T, ⟨(List.nodup_cons.mp h.1).2, hReadyT⟩, hStep⟩)
  exact ⟨T, hReadyT.2, hArrow⟩

/-- Natural target-cut data and fresh nontrivial steps preserving the
complete first-wagon refinements give the same selected Ramsey witness.
Initial tail bounds, initial refinements, freshness and all skipped steps
are supplied by the checked finite-pass construction. -/
theorem constructFromTargetCuts_of_freshNontrivialRefiningSteps
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
      e.toFunctionEmbedding ∉ remaining →
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
  obtain ⟨T, _, hArrow⟩ := constructFromInitial_of_freshNontrivialSteps A₀ B D family
    t ht targetTrain allowed hSupportNonempty hSupportCovers hGirth
    hTargetParameters hTail κ hBase ready hReady
    (fun _ _ _ h _ => ForestTailStage.FirstRefinementReady.tail h) actualStep
  exact ⟨T, hArrow⟩

end OrderedPass

end StructuralRamsey.Girth.TrainRecursiveWitness
