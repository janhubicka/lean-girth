import Girth.TrainCoverageFreePhysicalFibrePass
import Girth.TrainCoverageFreePhysicalRefinementReady
import Girth.TrainRecursiveRefinementReady
import Girth.TrainRecursiveWitnessProfiles
import Girth.TrainLabelledPhysicalToOrdinaryGirth

set_option autoImplicit false
set_option Elab.async false

namespace StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P : Type v}
/-- Assemble successive refining steps on a repetition-free profile list.
Refinements remain necessary only for the unprocessed profiles. -/
theorem ramseyForest_of_freshPhysicalRefiningSteps
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    [Finite P]
    (S : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed) (hm : 0 < (q :: tail).length) (g : ℕ) (κ : Type w) [Nonempty κ]
    (hInitial : PhysicalForestStage.FirstRefinementReady hm g (projectionProfileList UA P) S)
    (hInitialProject : S.system.toRelStructure.IsHomomorphism D S.system.part)
    (hBase : ∀ χ : Embedding A₀.ordered D → κ, ∃ b, b ∈ family ∧
      ∀ a₁ a₂ : Embedding A₀.ordered B, χ (b.comp a₁) = χ (b.comp a₂))
    (hLift : ∀ b ∈ family, ∃ r : DesignatedCopy B D S.system family,
      r ∈ S.selected ∧ r.base = b)
    (localStep : ∀ (e : Embedding A₀.ordered D) (remaining : List (UA ↪ P)) (T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed),
      PhysicalForestStage.CoversBase T →
      T.system.toRelStructure.IsHomomorphism D T.system.part →
      e.toFunctionEmbedding ∉ remaining →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered T.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      PhysicalForestStage.FirstRefinementReady hm g (e.toFunctionEmbedding :: remaining) T →
      ∃ R : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed, PhysicalForestStage.FirstRefinementReady hm g remaining R ∧
        R.system.toRelStructure.IsHomomorphism D R.system.part ∧
        PictureStep T R e.toFunctionEmbedding κ) :
    ∃ T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed, T.system.toRelStructure.IsHomomorphism D T.system.part ∧ DesignatedArrow T κ := by
  let Ready (profiles : List (UA ↪ P)) (T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed) :=
    profiles.Nodup ∧ PhysicalForestStage.FirstRefinementReady hm g profiles T ∧
      PhysicalForestStage.CoversBase T ∧ T.system.toRelStructure.IsHomomorphism D T.system.part
  have hReady : Ready (projectionProfileList UA P) S :=
    ⟨projectionProfileList_nodup, hInitial, hLift, hInitialProject⟩
  obtain ⟨T, hDone, hArrow⟩ := PhysicalForestStage.ramseyPass
    S (projectionProfileList UA P) κ Ready hReady
    mem_projectionProfileList hBase hLift (by
      intro α remaining T h
      have hNodup := (List.nodup_cons.mp h.1).2
      exact PhysicalForestStage.profileStep_of_nontrivialStep A₀ T α remaining κ Ready h
        (fun _ => ⟨hNodup, RemainingFirstRefinable.tail h.2.1, h.2.2⟩)
        (fun e hPair hE => by
          obtain ⟨R, hR, hProject, hStep⟩ := localStep e remaining T hE.2.2.1 hE.2.2.2
            (List.nodup_cons.mp hE.1).1 hPair hE.2.1
          exact ⟨R, ⟨hNodup, hR, PictureStep.coversBase hStep hE.2.2.1, hProject⟩, hStep⟩))
  exact ⟨T, hDone.2.2.2, hArrow⟩

/-- Start the physical finite pass from the actual disjoint target picture.
Labelled target cuts give the initial forest and tail bounds, and the
matching fibres give the initial first-wagon refinements. -/
theorem ramseyForest_fromTargetCuts_of_freshPhysicalRefiningSteps
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    {B : RelStructure L.withOrder VB} {D : RelStructure L.withOrder P}
    {family : Set (Embedding B D)} {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    [Finite VB] [Finite P] (ht : Admissible (q :: tail))
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A₀.ordered B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A₀.ordered B) q)
    (hTargetParameters : ∀ b : family, targetTrain.AdjacentParameters
      (fun edge => edge.1) (fun ν => b.val ⁻¹' allowed ν))
    (hTargetCuts : ∀ j : Fin (q :: tail).length, 0 < j.val → LabelledGirthGT
      (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc) ((q :: tail).get j))
    (g : ℕ) (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : Embedding A₀.ordered D → κ, ∃ b, b ∈ family ∧
      ∀ a₁ a₂ : Embedding A₀.ordered B, χ (b.comp a₁) = χ (b.comp a₂))
    (localStep : ∀ (e : Embedding A₀.ordered D) (remaining : List (UA ↪ P)) (T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed),
      PhysicalForestStage.CoversBase T →
      T.system.toRelStructure.IsHomomorphism D T.system.part →
      e.toFunctionEmbedding ∉ remaining →
      (∃ a b : StructuralRamsey.Partite.ProjectedEmbedding A₀.ordered T.system e.toFunctionEmbedding,
        copyCarrier a.val ≠ copyCarrier b.val) →
      PhysicalForestStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty) g
        (e.toFunctionEmbedding :: remaining) T →
      ∃ R : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed, PhysicalForestStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty) g remaining R ∧
        R.system.toRelStructure.IsHomomorphism D R.system.part ∧
        PictureStep T R e.toFunctionEmbedding κ) :
    ∃ T : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed, T.system.toRelStructure.IsHomomorphism D T.system.part ∧ DesignatedArrow T κ := by
  letI : Nonempty family := by
    obtain ⟨b, hb⟩ := baseFamily_nonempty_of_arrow A₀.ordered B D family κ hBase
    exact ⟨⟨b, hb⟩⟩
  let hA : A₀.ordered.Irreducible := (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  let hTail := initialTail_of_targetCuts A₀.ordered hA B D family (q :: tail) ht targetTrain
    hSupportNonempty hGirth hTargetCuts
  let old := initialForestTailStage_of_tail A₀.ordered hA B D family (q :: tail) ht targetTrain allowed
    hSupportNonempty hSupportCovers hGirth hTargetParameters hTail
  let S : PhysicalForestStage A₀.ordered B D family (q :: tail) targetTrain allowed := PhysicalForestStage.ofStrong hA (ForestStage.ofStrong old)
  refine ramseyForest_of_freshPhysicalRefiningSteps A₀ S
    (List.length_pos_iff.mpr ht.nonempty) g κ ?_ old.isPartite.1 hBase ?_ localStep
  · exact initialForestTailStage_firstRefinementReady A₀.ordered hA B D family (q :: tail) ht
      targetTrain allowed hSupportNonempty hSupportCovers hGirth hTargetParameters
      hTail g (projectionProfileList UA P)
  · intro b hb
    exact ⟨initialDesignatedCopy B D family ⟨b, hb⟩, Set.mem_range_self _, rfl⟩

end StructuralRamsey.Girth.TrainRecursiveWitness.CoverageFree.Physical
