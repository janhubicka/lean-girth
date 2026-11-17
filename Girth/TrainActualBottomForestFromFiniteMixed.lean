import Girth.TrainActualBottomFullSystemForestPreservation
import Girth.TrainActualWitnessBottomMixedForestBridge
import Girth.ForestRecursiveOutputGirth
import Girth.AttachmentStrongness

set_option autoImplicit false
set_option Elab.async false

/-!
# Direct finite mixed F_t input to actual bottom full system girth

The one-step bottom theorem no longer needs full witness system
girth. In the non-one-edge case it can be instantiated directly from
the exact SAME-CUTOFF finite set-valued mixed forest hypothesis:

* testing every real ambient A-edge yields ordinary A-girth >q
  and therefore A-linearity in the local witness;
* testing every whole gluing-copy A-support yields A-strongness of
  that gluing image;
* physical injectivity of chosen gluing-copy supports and two
  different source A-edges upgrade finite sets to labelled
  LocalForestThrough without duplicating B-supports;
* the genuine free attachment has A-linear physical output edges;
* the checked shared/whole-gluing witness equality transports
  precisely this bottom local forest to the reduction's literal
  shared-witness order-one incidence model;
* the actual bottom full-system theorem preserves ORIGINAL B labels.

No lower-rank recursive witness or output system-girth is assumed.
This is the main cut-zero building block of the finite F_t -> R_t
conversion. Positive train coordinates remain a separate pass.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualBottomForestFromFiniteMixed

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D) (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hShared : ∀ _i : I, Nonempty
  (SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)))
variable (hRel : ∀ (ν : Fin (m + 1)) (j : I)
  (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν (sharedOldACarrierCoreEmbedding A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f j p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f j q))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Active" => (C.toRelStructure.induce S)
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μBottom
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "Local" => activeGluingWitnessOrderOneData
  A C e.toFunctionEmbedding R f U μBottom
local notation "Wit" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "Tested" => RelationalMixedSupportTest A f

include hRel

/-- Genuine bottom preservation at the SAME q from the actual F_t
finite SET mixed forest condition. Old full girth and standard
gluing geometry are the only old-picture inputs; every local
A-support edge and every original selected B label is retained. -/
theorem attachedSelectedPicture_bottom_fullSystemGirth_of_finiteMixed
    [Finite UA] [Nontrivial UA]
    (q : ℕ) (hq : 2 ≤ q)
    (hOld : (Old).FullSystemGirthGT q)
    (hBaseStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoSelected : ∀ r : Selected,
      ∃ a b : OldACarrierEdge A C.toRelStructure,
        a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
          b.1 ⊆ copyCarrier r.1.embedding)
    (hActiveStrong : AStrong A C.toRelStructure S)
    (a b : RelStructure.Embedding A Active)
    (hTwoSource : ¬ SameCopy a b)
    (hChosenImages : Function.Injective
      (fun i : I => copyCarrier (f i)))
    (hMixed : FiniteMixedForestThrough Tested q) :
    (Out).FullSystemGirthGT q := by
  have hCoreGirth : GirthGT (supportCopies A R) q := by
    apply girthGT_of_finiteMixedForestThrough
      (supportCopies A R) Tested q hMixed
    rintro edge ⟨a, rfl⟩
    exact Or.inr ⟨a, rfl⟩
  have hCoreLinear : ALinear A R :=
    aLinear_of_girthGT_two A R
      (girthGT_mono hCoreGirth hq)
  have hCoreStrong : ∀ i : I,
      AStrong A R (copyCarrier (f i)) := by
    intro i
    exact aStrong_of_finiteMixedForestThrough
      A (f i) Tested q hq hMixed
      (Or.inl ⟨i, rfl⟩) (fun a => Or.inr ⟨a, rfl⟩)
  have hOldLinear : ALinear A C.toRelStructure :=
    aLinear_of_oldACarrier_edges_inter_subsingleton
      A C.toRelStructure hOld.1.1
  have hPhysical : ALinear A Actual :=
    attachment_aLinear C.toRelStructure S R f hA
      hOldLinear hCoreLinear hActiveStrong hCoreStrong
  let HLocal : (Local).BottomForestGeometry :=
    activeGluingWitness_bottomForestGeometry
      A C e.toFunctionEmbedding R f U hCoreLinear
  have hLocal : LocalForestThrough
      ((Local).bottomForestPiece HLocal) q :=
    activeGluingWitness_bottom_localForest_of_finiteMixed
      A C e.toFunctionEmbedding R f U HLocal
      a b hTwoSource
      (activeGluingWitness_supportPiece_injective_of_distinct_images
        A C e.toFunctionEmbedding R f hChosenImages)
      q hMixed
  have hSharedWitness :
      ∃ H : (Wit).BottomForestGeometry,
        LocalForestThrough ((Wit).bottomForestPiece H) q := by
    rw [← activeGluingWitnessOrderOneData_eq_shared
      A C e.toFunctionEmbedding R f U μBottom]
    exact ⟨HLocal, hLocal⟩
  obtain ⟨HWit, hWitLocal⟩ := hSharedWitness
  exact attachedSelectedPicture_bottom_fullSystemGirth_of_localForest
    A hA B D C family selected e R f T U hShared hRel
    hPhysical hBaseStrong hTwoSelected hActiveStrong hCoreStrong
    HWit q hWitLocal hOld.2

end ActualBottomForestFromFiniteMixed
end StructuralRamsey.Girth
