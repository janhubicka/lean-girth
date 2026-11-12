import Girth.TrainActualOneLevelGirthIntrinsic
import Girth.TrainRecursiveWitnessPass

set_option autoImplicit false
set_option Elab.async false

/-!
# Track B: all positive attached tail supreme certificates from intrinsic geometry

The old selected ForestTailStage already carries FullSystemGirthGT at
each positive original cut. A real lower shared gluing witness, at the
SAME original cutoff, supplies its second full-system input.

The exact original-source Path A one-level theorem now derives output
linearity and all core-image A-strongness from the old stage's genuine
A-partiteness, the A-linear base and rigidity, and this lower witness's
FullSystemGirthGT. Thus no independent output linearity, core-image
strongness, arbitrary hTail oracle, or output FullSystemGirthGT premise
appears here. The two old B-support edges in every selected B-copy are
derived from one actual two-copy witness for the target B.

The statement returns ALL original positive tail SupremeCycleBound
values t[j], not merely q=the leading cutoff. For monotone cutoff
vectors, the exact retained-cut transfer is checked independently in
TrainRecursiveExactOriginalRetainedCutoff and
TrainRecursiveExactRetainedFullSystemGirth.

The actual lower positive full-system certificates, base strongness,
literal shared-core train restriction, and genuine lower Ramsey stage
must still be obtained by the recursive construction. This theorem
does not assert that existence or finish the nontrivial PictureStep.
No appendix or manuscript markers are changed.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P Y I : Type v}

variable (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
variable (B : RelStructure L VB) (D : RelStructure L P)
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (S : ForestTailStage A B D family t targetTrain allowed)
variable (e : Embedding A D)
variable (R : RelStructure L Y)
variable (f : I → Embedding
  (S.system.toRelStructure.induce
    (activeCarrier A S.system e.toFunctionEmbedding)) R)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) t.length)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A S.system e.toFunctionEmbedding)

local notation "hShared" =>
  activeCarrier_all_standard_copies_meet_core
    A S.system e.toFunctionEmbedding active I
local notation "Selected" =>
  {b : DesignatedCopy B D S.system family // b ∈ S.selected}
local notation "OldEdge" => OldACarrierEdge A S.system.toRelStructure
local notation "Out" => fun ν : Fin (t.length + 1) =>
  attachedSelectedPictureOrderOneData
    A hA B D S.system family S.selected e R f S.train U hShared ν
local notation "Wit" => fun ν : Fin (t.length + 1) =>
  sharedWitnessOrderOneData U ν
    (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
      (activeCarrier A S.system e.toFunctionEmbedding) R f)
    (Subtype.val : OldACarrierEdge A R → Set Y)

variable (hRel : ∀ (ν : Fin (t.length + 1)) (i : I)
  (p q : SharedOldACarrierEdge A S.system.toRelStructure
    (activeCarrier A S.system e.toFunctionEmbedding)),
  S.train.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
      (activeCarrier A S.system e.toFunctionEmbedding) R f i p)
      (sharedOldACarrierCoreEmbedding A S.system.toRelStructure
        (activeCarrier A S.system e.toFunctionEmbedding) R f i q))

include hRel

/-- All ORIGINAL positive tail supremeness bounds of the actual
attached selected picture, directly from genuine old and lower
FullSystemGirthGT at the original thresholds. Output geometry is
DERIVED by the intrinsic Path A theorem, not postulated. -/
theorem ForestTailStage.attachedAllPositiveSupreme_of_intrinsicWitness
    (hTwoCut : ∀ j : Fin t.length, 0 < j.val → 2 ≤ t.get j)
    (hStrong : ∀ r : Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTargetTwo : ∃ a b : Embedding A B, ¬ SameCopy a b)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hWitness : ∀ j : Fin t.length, 0 < j.val →
      (Wit j.castSucc).FullSystemGirthGT (t.get j)) :
    ∀ j : Fin t.length, 0 < j.val →
      (Out j.castSucc).SupremeCycleBound (t.get j) := by
  have hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding := by
    obtain ⟨a, b, hab⟩ := hTargetTwo
    intro r
    refine ⟨actualEdge (r.1.embedding.comp a),
      actualEdge (r.1.embedding.comp b), ?_, ?_, ?_⟩
    · intro heq
      apply hab
      apply sameCopy_of_comp r.1.embedding
      change copyCarrier (r.1.embedding.comp a) =
        copyCarrier (r.1.embedding.comp b)
      exact congrArg (fun edge : OldEdge => edge.1) heq
    · change copyCarrier (r.1.embedding.comp a) ⊆
        copyCarrier r.1.embedding
      rintro x ⟨u, rfl⟩
      exact ⟨a u, rfl⟩
    · change copyCarrier (r.1.embedding.comp b) ⊆
        copyCarrier r.1.embedding
      rintro x ⟨u, rfl⟩
      exact ⟨b u, rfl⟩
  intro j hj
  have hOutFull :
      (Out j.castSucc).FullSystemGirthGT (t.get j) :=
    attachedSelectedPicture_fullSystemGirth_of_intrinsic_geometry
      A hA B D S.system family S.selected e R f S.train U
      hShared hRel j.castSucc
      S.isPartite hBaseLinear hRigid hStrong hTwoCopies
      (t.get j) (hTwoCut j hj)
      (S.tailGirth j hj) (hWitness j hj)
  exact hOutFull.2

end StructuralRamsey.Girth.TrainRecursiveWitness
