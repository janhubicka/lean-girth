import Girth.TrainActualSameVectorForestCoordinates
import Girth.TrainActualIntrinsicParameters
import Girth.TrainSharedSupportInteriorCompatibility
import Girth.TrainFullSystemGirthParameter

set_option autoImplicit false
set_option Elab.async false

/-!
# Same-vector bottom forests, interior system girth AND exact parameters

A real partite attachment is built at one fixed vector (q) ++ h.
The old picture and actual local witness carry the same family of
allowed part sets and the same shared-support train restrictions.

The previous coordinatewise theorem gives output full system girth
at the BOTTOM q and at EACH positive proper cutoff h_i. Here we
also reuse the checked intrinsic parameter theorem: positive proper
local full system girth implies exactly the order-one bridge it
needs. The bottom equality relation and universal top relation
supply both endpoint compatibilities without a top system-girth
or an invented new recursive witness.

This package intentionally does not construct the finite Ramsey
arrow or the coarsened final partite train. Those are the remaining
finite-conversion assembly obligations.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section SameVectorWithParameters

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding
  A C e.toFunctionEmbedding)
variable (E : StructuralRamsey.Partite.System L P Y)
variable (f : I → StructuralRamsey.Partite.Embedding
  (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) m)

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "RF" => (fun i : I => (f i).toEmbedding)
local notation "Shared" => activeCarrier_all_standard_copies_meet_core
  A C e.toFunctionEmbedding active I
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S E.toRelStructure RF T U Shared
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Bottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Old" => (fun μ : Fin (m + 1) =>
  selectedPictureOrderOneData A B D C family selected T μ)
local notation "Wit" => (fun μ : Fin (m + 1) =>
  sharedWitnessOrderOneData U μ
    (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure RF)
    (Subtype.val : OldACarrierEdge A E.toRelStructure → Set Y))
local notation "Out" => (fun μ : Fin (m + 1) =>
  attachedSelectedPictureOrderOneData A hA B D C family selected
    e E.toRelStructure RF T U Shared μ)

/-- At the SAME vector, an actual selected forest witness and exact
positive local system-girth bounds give all required non-top output
system-girth bounds AND the actual adjacent-part intersection
parameters. The required selected family has one label per image.
No universal-top girth bound is postulated. -/
theorem attachedSelectedPicture_sameVector_bounds_and_parameters
    [Finite UA] [Nontrivial UA]
    (hPartite : C.IsPartiteOver D)
    (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D,
      SameCopy b e → b = e)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoSelected : ∀ q : Selected,
      ∃ a b : OldACarrierEdge A C.toRelStructure,
        a ≠ b ∧ a.1 ⊆ copyCarrier q.1.embedding ∧
          b.1 ⊆ copyCarrier q.1.embedding)
    (cutoff : Fin (m + 1) → ℕ)
    (hBottomTwo : 2 ≤ cutoff Bottom)
    (hPositiveTwo : ∀ μ : Fin (m + 1),
      0 < μ.val → μ.val < m → 2 ≤ cutoff μ)
    (hOld : ∀ μ : Fin (m + 1),
      (μ = Bottom ∨ (0 < μ.val ∧ μ.val < m)) →
      (Old μ).FullSystemGirthGT (cutoff μ))
    (a b : RelStructure.Embedding A (C.toRelStructure.induce S))
    (hTwoSource : ¬ SameCopy a b)
    (hSelectedImages : Function.Injective
      (fun i : I => copyCarrier (RF i)))
    (hBottomMixed : FiniteMixedForestThrough
      (RelationalMixedSupportTest A RF) (cutoff Bottom))
    (hPositive : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Wit μ).FullSystemGirthGT (cutoff μ))
    (allowedParts : Fin (m + 1) → Set P)
    (hOldParams : T.AdjacentParameters
      (fun edge : OldACarrierEdge A C.toRelStructure => edge.1)
      (fun ν => {x | C.part x ∈ allowedParts ν}))
    (hCoreParams : U.AdjacentParameters
      (fun edge : OldACarrierEdge A E.toRelStructure => edge.1)
      (fun ν => {x | E.part x ∈ allowedParts ν}))
    (hInterior : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      ∀ (i : I) (p q : SharedOldACarrierEdge A C.toRelStructure S),
        T.rel μ p.1 q.1 ↔
          U.rel μ
            (sharedOldACarrierCoreEmbedding A C.toRelStructure
              S E.toRelStructure RF i p)
            (sharedOldACarrierCoreEmbedding A C.toRelStructure
              S E.toRelStructure RF i q)) :
    (Out Bottom).FullSystemGirthGT (cutoff Bottom) ∧
    (∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Out μ).FullSystemGirthGT (cutoff μ)) ∧
    Train.AdjacentParameters
      (fun edge : ActualAttachedAEdge A C.toRelStructure S E.toRelStructure RF =>
        edge.1)
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach C S E f).part x ∈
          allowedParts ν}) := by
  have hRel : ∀ (ν : Fin (m + 1)) (j : I)
      (p q : SharedOldACarrierEdge A C.toRelStructure S),
      T.rel ν p.1 q.1 ↔
      U.rel ν
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          S E.toRelStructure RF j p)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          S E.toRelStructure RF j q) := by
    apply sharedSupportTrainRel_of_interior T U
      (sharedOldACarrierInclusion A C.toRelStructure S)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure S E.toRelStructure RF)
    intro ν hZero hTop j p q
    exact hInterior ν (by omega) (by omega) j p q
  have hBounds :=
    attachedSelectedPicture_bottom_and_interior_of_sameVector
      A hA B D C family selected e E.toRelStructure RF
      T U Shared hRel
      hPartite hBaseLinear hRigid hStrong hTwoSelected
      cutoff hBottomTwo hPositiveTwo hOld
      a b hTwoSource hSelectedImages hBottomMixed hPositive
  have hParameters : Train.AdjacentParameters
      (fun edge : ActualAttachedAEdge A C.toRelStructure S E.toRelStructure RF =>
        edge.1)
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach C S E f).part x ∈
          allowedParts ν}) := by
    apply activeAttached_actualASupport_allAdjacentParameters_of_intrinsic
      A hA C e.toFunctionEmbedding active E f T U allowedParts
      hOldParams hCoreParams hInterior
    intro ν hPos hLt
    exact OrderOneData.bound_of_fullSystemGirth_ge_one
      (Wit ν) (cutoff ν) (by omega) (hPositive ν hPos hLt)
  exact ⟨hBounds.1, hBounds.2, hParameters⟩

end SameVectorWithParameters
end StructuralRamsey.Girth
