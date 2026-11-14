import Girth.TrainActualBottomForestFromFiniteMixed
import Girth.TrainActualOneLevelGirthIntrinsic
import Girth.ActiveCarrierStrong

set_option autoImplicit false
set_option Elab.async false

/-!
# One finite same-vector pass: bottom forest, positive full-system cuts

The forest-to-order conversion does NOT invoke the recursive witness
at a smaller vector. At its current fixed vector it calls the forest
lemma on the active subsystem:

* bottom q: the genuine finite-SET mixed forest through exactly q
  gives the bottom output FullSystemGirthGT q;
* each positive PROPER cut: the already checked full-system
  alternative transfers the genuine old and local full bound at its
  OWN cutoff h_i, possibly larger than q.

The universal top cut and final finite Ramsey arrow/part-order
bookkeeping are intentionally not asserted. This module packages
only what the preservation theorem supplies at each non-top cut,
with no lowering of the positive thresholds to q or 2.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section SameVectorForestCoordinates

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
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Old" => (fun μ : Fin (m + 1) =>
  selectedPictureOrderOneData A B D C family selected T μ)
local notation "Wit" => (fun μ : Fin (m + 1) =>
  sharedWitnessOrderOneData U μ
    (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
    (Subtype.val : OldACarrierEdge A R → Set Y))
local notation "Out" => (fun μ : Fin (m + 1) =>
  attachedSelectedPictureOrderOneData
    A hA B D C family selected e R f T U hShared μ)
local notation "Tested" => RelationalMixedSupportTest A f

include hRel

/-- Actual same-vector preservation at the bottom and all positive
PROPER cuts. The finite mixed local forest is requested at q exactly,
while every positive proper full local witness bound is requested at
its OWN cutoff. This statement asserts neither top-cut treatment
nor existence of the local Ramsey witness or finite partite arrow. -/
theorem attachedSelectedPicture_bottom_and_interior_of_sameVector
    [Finite UA] [Nontrivial UA]
    (hPartite : C.IsPartiteOver D)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D,
      SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoSelected : ∀ r : Selected,
      ∃ a b : OldACarrierEdge A C.toRelStructure,
        a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
          b.1 ⊆ copyCarrier r.1.embedding)
    (cutoff : Fin (m + 1) → ℕ)
    (hBottomTwo : 2 ≤ cutoff μBottom)
    (hPositiveTwo : ∀ μ : Fin (m + 1),
      0 < μ.val → μ.val < m → 2 ≤ cutoff μ)
    (hOld : ∀ μ : Fin (m + 1),
      (μ = μBottom ∨ (0 < μ.val ∧ μ.val < m)) →
      (Old μ).FullSystemGirthGT (cutoff μ))
    (a b : RelStructure.Embedding A Active)
    (hTwoSource : ¬ SameCopy a b)
    (hChosenImages : Function.Injective
      (fun i : I => copyCarrier (f i)))
    (hBottomMixed : FiniteMixedForestThrough Tested (cutoff μBottom))
    (hFullPositive : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Wit μ).FullSystemGirthGT (cutoff μ)) :
    (Out μBottom).FullSystemGirthGT (cutoff μBottom) ∧
      ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
        (Out μ).FullSystemGirthGT (cutoff μ) := by
  have hActiveStrong : AStrong A C.toRelStructure S :=
    activeCarrier_aStrong_of_base_aLinear
      A D C hA hPartite hBaseLinear e hRigid
  constructor
  · exact attachedSelectedPicture_bottom_fullSystemGirth_of_finiteMixed
      A hA B D C family selected e R f T U hShared hRel
      (cutoff μBottom) hBottomTwo
      (hOld μBottom (Or.inl rfl))
      hStrong hTwoSelected hActiveStrong
      a b hTwoSource hChosenImages hBottomMixed
  · intro μ hPos hLt
    exact attachedSelectedPicture_fullSystemGirth_of_intrinsic_geometry
      A hA B D C family selected e R f T U hShared hRel μ
      hPartite hBaseLinear hRigid hStrong hTwoSelected
      (cutoff μ) (hPositiveTwo μ hPos hLt)
      (hOld μ (Or.inr ⟨hPos, hLt⟩))
      (hFullPositive μ hPos hLt)

end SameVectorForestCoordinates
end StructuralRamsey.Girth
