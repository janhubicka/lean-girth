import Girth.TrainRecursiveActualRetainedSelectedWitnessGirth
import Girth.TrainRecursiveIntrinsicTailSupreme
import Girth.TrainRecursiveFineWitnessTransport
import Girth.TrainRecursiveCoarsenedSelectedRestriction

set_option autoImplicit false
set_option Elab.async false

/-!
# Actual lower selected witness implies the attached original tail bounds

The lower-rank recursion uses the full refined true active subsystem,
with lower cutoff vector
  replicate (R.extraCuts + 1) (q - 1) ++ tail.
Its train is the genuine refinement of the old active train, transported
by the arithmetically exact height equality. A REAL selected lower
ForestTailStage already stores the full target train restriction and all
positive system-girth bounds.

This module composes three existing results:
* literal selected-copy restriction gives the old shared train relation
  after forgetting inserted cuts, including equality and top;
* the real lower stage's positive girth at original retained thresholds
  gives actual shared-witness FullSystemGirthGT at every tail coordinate;
* the intrinsic full-system preservation theorem gives attached OUTPUT
  SupremeCycleBound at the original cutoff for every positive tail cut.

Thus output hTail and the coarse relation hRel are conclusions, not
independent hypotheses. No lower-stage existence, nontrivial PictureStep
or universal recursive train theorem is asserted. In particular the
whole old base family must genuinely be A-strong, as required by the
intrinsic cycle preservation theorem.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P V : Type v}

/-- A height cast changes only the Fin coordinate; it changes no
edge, wagon, or label relation. -/
private theorem castHeight_rel_iff_selected
    {W : Type v} {m n : ℕ}
    (S : EdgeTrainLevels W m) (h : m = n)
    (ν : Fin (n + 1)) (a b : W) :
    (S.castHeight h).rel ν a b ↔
      S.rel (Fin.cast (congrArg (fun k : ℕ => k + 1) h).symm ν) a b := by
  cases h
  rfl

/-- The genuine lower forest stage supplies ALL actual attached positive
tail SupremeCycleBound values, without any hRel, hWitness or hTail
oracle. All selected physical labels and all ambient edges are retained.

The assumptions on the old base family and base geometry are the
explicit hypotheses of the existing intrinsic one-level preservation
theorem; they are not inferred from the lower stage. -/
theorem ForestTailStage.attachedAllPositiveSupreme_of_refinedSelectedLower
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    {family : Set (Embedding B D)}
    {q : ℕ} {tail : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) (q :: tail).length}
    {allowed : Fin ((q :: tail).length + 1) → Set P}
    (old : ForestTailStage A B D family (q :: tail) targetTrain allowed)
    (e : Embedding A D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A old.system e.toFunctionEmbedding)
    (R : FirstWagonRefinement
      (old.train.restrict (sharedOldACarrierInclusion
        A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding)))
      (by simp : 0 < (q :: tail).length)
      (fun edge => edge.1.1) old.system.part
      (allowed ⟨1, by simp⟩) (q - 1))
    (Large : StructuralRamsey.Partite.System L UA V)
    {lowerFamily : Set (Embedding
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure)}
    {lowerAllowed : Fin
      ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length + 1) → Set V}
    (lower : ForestTailStage A
      (old.system.toRelStructure.induce
        (activeCarrier A old.system e.toFunctionEmbedding))
      Large.toRelStructure lowerFamily
      (List.replicate (R.extraCuts + 1) (q - 1) ++ tail)
      ((R.train.restrict (inducedACarrierToShared
        A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding))).castHeight
        (actualReplicatedCutoff_height_eq q R.extraCuts tail).symm)
      lowerAllowed)
    (hFamilyParts : ∀ b, b ∈ lowerFamily →
      ∀ x : activeCarrier A old.system e.toFunctionEmbedding,
        Large.part (b x) =
          activeSourcePart A old.system e.toFunctionEmbedding x)
    (hTwoCut : ∀ j : Fin (q :: tail).length, 0 < j.val →
      2 ≤ (q :: tail).get j)
    (hStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e) :
    let Target := actualActiveSubsystemPartite A old.system
      e.toFunctionEmbedding
    let E := lower.system.coarsenVia Large lower.isPartite
    let I := {b : DesignatedCopy Target.toRelStructure
      Large.toRelStructure lower.system lowerFamily // b ∈ lower.selected}
    let f : I → Embedding Target.toRelStructure E.toRelStructure :=
      fun i => (selectedPartiteGluingFamily_of_largeBase
        Target Large lower.system lower.isPartite
        lowerFamily hFamilyParts lower.selected i).toEmbedding
    let T := lower.train.castHeight
      (actualReplicatedCutoff_height_eq q R.extraCuts tail)
    ∀ j : Fin (q :: tail).length, 0 < j.val →
      (attachedSelectedPictureOrderOneData A hA B D old.system
        family old.selected e E.toRelStructure f old.train
        (T.forgetFirstCuts (by simp : 0 < (q :: tail).length))
        (activeCarrier_all_standard_copies_meet_core
          A old.system e.toFunctionEmbedding active I)
        j.castSucc).SupremeCycleBound ((q :: tail).get j) := by
  classical
  let Target := actualActiveSubsystemPartite A old.system e.toFunctionEmbedding
  let E := lower.system.coarsenVia Large lower.isPartite
  let I := {b : DesignatedCopy Target.toRelStructure Large.toRelStructure
    lower.system lowerFamily // b ∈ lower.selected}
  let f : I → Embedding Target.toRelStructure E.toRelStructure :=
    fun i => (selectedPartiteGluingFamily_of_largeBase
      Target Large lower.system lower.isPartite lowerFamily
      hFamilyParts lower.selected i).toEmbedding
  let hLen := actualReplicatedCutoff_height_eq q R.extraCuts tail
  let T := lower.train.castHeight hLen
  let U := T.forgetFirstCuts (by simp : 0 < (q :: tail).length)
  let SourceCut := R.train.restrict (inducedACarrierToShared
    A old.system.toRelStructure
    (activeCarrier A old.system e.toFunctionEmbedding))
  have hFine : ∀ (ν : Fin ((q :: tail).length + R.extraCuts + 1))
      (i : I) (a b : Embedding A Target.toRelStructure),
      T.rel ν (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b)) ↔
        SourceCut.rel ν (actualEdge a) (actualEdge b) := by
    intro ν i a b
    let νLower : Fin
        ((List.replicate (R.extraCuts + 1) (q - 1) ++ tail).length + 1) :=
      Fin.cast (congrArg (fun k : ℕ => k + 1) hLen).symm ν
    have hBack :
        Fin.cast (congrArg (fun k : ℕ => k + 1) hLen.symm).symm νLower =
          ν := Fin.ext rfl
    have hRaw := lower.coarsenedSelected_trainRestriction
      A Target Large hFamilyParts νLower i a b
    have hRHS :
        lower.train.rel νLower
          (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b)) ↔
        SourceCut.rel ν (actualEdge a) (actualEdge b) := by
      simpa only [castHeight_rel_iff_selected, hBack] using hRaw
    exact (castHeight_rel_iff_selected lower.train hLen ν
      (actualEdge ((f i).comp a)) (actualEdge ((f i).comp b))).trans hRHS
  have hRel : ∀ (ν : Fin ((q :: tail).length + 1)) (i : I)
      (p s : SharedOldACarrierEdge A old.system.toRelStructure
        (activeCarrier A old.system e.toFunctionEmbedding)),
      old.train.rel ν p.1 s.1 ↔
        U.rel ν (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
          (activeCarrier A old.system e.toFunctionEmbedding)
          E.toRelStructure f i p)
          (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
            (activeCarrier A old.system e.toFunctionEmbedding)
            E.toRelStructure f i s) := by
    intro ν i p s
    exact coarseSharedTrain_iff_of_finePrescribedRestriction
      A old.system.toRelStructure
      (activeCarrier A old.system e.toFunctionEmbedding)
      E.toRelStructure f old.train (by simp) R T hFine ν i p s
  have hWitness : ∀ j : Fin (q :: tail).length, 0 < j.val →
      (sharedWitnessOrderOneData U j.castSucc
        (sharedOldACarrierCoreEmbedding A old.system.toRelStructure
          (activeCarrier A old.system e.toFunctionEmbedding)
          E.toRelStructure f)
        (Subtype.val : OldACarrierEdge A E.toRelStructure → Set lower.Vertex)
      ).FullSystemGirthGT ((q :: tail).get j) := by
    exact lower.coarsenedSelected_retainedSharedFullSystem_of_realStage
      A old.system e.toFunctionEmbedding Large hFamilyParts
  dsimp only
  exact ForestTailStage.attachedAllPositiveSupreme_of_intrinsicWitness
    A hA B D old e E.toRelStructure f U active hRel
    hTwoCut hStrong hTargetTwo hBaseLinear hRigid hWitness

end StructuralRamsey.Girth.TrainRecursiveWitness
