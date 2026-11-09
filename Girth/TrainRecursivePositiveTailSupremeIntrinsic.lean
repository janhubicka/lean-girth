import Girth.TrainActualOneLevelGirthIntrinsic
import Girth.TrainRecursiveWitnessPass
import Girth.ActiveCarrierStrong

set_option autoImplicit false
set_option Elab.async false

/-!
# Positive attached tail supremacy from the intrinsic original output theorem

The actual old ForestTailStage already supplies complete original
selected-picture FullSystemGirthGT at every positive old cut.
Assume the genuine lower shared witness's COMPLETE FullSystemGirthGT
at the corresponding original t[j] and the actual physical shared
train relations. The now certified original two-cycle/longer-cycle
intrinsic output theorem then proves the attached output's full
system girth and hence its SupremeCycleBound at each such cut.

This proof does NOT re-assume output LinearPretrain, A-strongness of
the old active fibre, A-strongness of the gluing images, or two old
physical edges per selected B-copy: all are derived from the actual
old stage, the lower witness and two different A-copies inside B.
No fictitious original B-label, geometric owner quotient or edge
deletion is introduced. A real lower witness with the required
retained t[j] cuts remains a separate induction obligation.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}

/-- The genuine old selected stage and a lower shared full-system
witness imply EVERY positive original attached SupremeCycleBound.
No independently postulated output girth or linearity input. -/
theorem ForestTailStage.attachedAllPositiveSupreme_of_intrinsicWitness
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    {family : Set (Embedding B D)} {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (S : ForestTailStage A B D family t targetTrain allowed)
    (e : Embedding A D)
    (R : RelStructure L Y)
    (f : I → Embedding
      (S.system.toRelStructure.induce
        (activeCarrier A S.system e.toFunctionEmbedding)) R)
    (U : EdgeTrainLevels (OldACarrierEdge A R) t.length)
    (active : StructuralRamsey.Partite.ProjectedEmbedding
      A S.system e.toFunctionEmbedding)
    (hRel : ∀ (ν : Fin (t.length + 1)) (i : I)
      (p q : SharedOldACarrierEdge A S.system.toRelStructure
        (activeCarrier A S.system e.toFunctionEmbedding)),
      S.train.rel ν p.1 q.1 ↔
        U.rel ν
          (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
            (activeCarrier A S.system e.toFunctionEmbedding) R f i p)
          (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
            (activeCarrier A S.system e.toFunctionEmbedding) R f i q))
    (hCut : ∀ j : Fin t.length, 0 < j.val → 2 ≤ t.get j)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hBaseStrong : ∀ b : Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hWitness : ∀ j : Fin t.length, 0 < j.val →
      (sharedWitnessOrderOneData U j.castSucc
        (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
          (activeCarrier A S.system e.toFunctionEmbedding) R f)
        (Subtype.val : OldACarrierEdge A R → Set Y)).FullSystemGirthGT
        (t.get j)) :
    ∀ j : Fin t.length, 0 < j.val →
      (attachedSelectedPictureOrderOneData
        A hA B D S.system family S.selected e R f S.train U
        (activeCarrier_all_standard_copies_meet_core
          A S.system e.toFunctionEmbedding active I)
        j.castSucc).SupremeCycleBound (t.get j) := by
  classical
  have hTwoCopies :
      ∀ r : {b : DesignatedCopy B D S.system family // b ∈ S.selected},
        ∃ a b : OldACarrierEdge A S.system.toRelStructure,
          a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
            b.1 ⊆ copyCarrier r.1.embedding := by
    obtain ⟨a, b, hDistinct⟩ := hTargetTwo
    intro r
    refine ⟨actualEdge (r.1.embedding.comp a),
      actualEdge (r.1.embedding.comp b), ?_, ?_, ?_⟩
    · intro hab
      apply hDistinct
      apply sameCopy_of_comp r.1.embedding
      change copyCarrier (r.1.embedding.comp a) =
        copyCarrier (r.1.embedding.comp b)
      exact congrArg
        (fun edge : OldACarrierEdge A S.system.toRelStructure => edge.1) hab
    · change copyCarrier (r.1.embedding.comp a) ⊆
        copyCarrier r.1.embedding
      rintro x ⟨u, rfl⟩
      exact ⟨a u, rfl⟩
    · change copyCarrier (r.1.embedding.comp b) ⊆
        copyCarrier r.1.embedding
      rintro x ⟨u, rfl⟩
      exact ⟨b u, rfl⟩
  intro j hj
  let hShared := activeCarrier_all_standard_copies_meet_core
    A S.system e.toFunctionEmbedding active I
  have hOld :
      (selectedPictureOrderOneData A B D S.system family
        S.selected S.train j.castSucc).FullSystemGirthGT (t.get j) :=
    S.tailGirth j hj
  have hOut :=
    attachedSelectedPicture_fullSystemGirth_of_intrinsic_geometry
      A hA B D S.system family S.selected e R f S.train U
      hShared hRel j.castSucc
      S.isPartite hBaseLinear hRigid hBaseStrong hTwoCopies
      (t.get j) (hCut j hj) hOld (hWitness j hj)
  exact hOut.2

end StructuralRamsey.Girth.TrainRecursiveWitness
