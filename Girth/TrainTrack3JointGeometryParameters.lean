import Girth.TrainSelectedPictureIntrinsicGeometry
import Girth.TrainActualIntrinsicParameters
import Girth.TrainFullSystemGirthParameter

set_option autoImplicit false
set_option Elab.async false

/-!
# Numbered Track 3: joint intrinsic output geometry and train parameters

The same real lower witness bound supplies the order-two pieces needed for
output wagon linearity and the order-one bridges needed for adjacent allowed
part parameters. This packages existing proved implications; no output girth,
new source oracle or designated-copy coverage assumption is used.

This new wrapper is an UNCOMPILED candidate until checked with the pinned
local toolchain and the strict axiom gate. Existing imported theorems were
previously kernel-verified. Printed manuscript target: girth/main@8c9cfa6e.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}

/-- The pinned partite dependency literally induces the same underlying
relational substructure. No isomorphism or new hypothesis is involved. -/
theorem track3_partiteInduce_toRelStructure_eq
    (C : StructuralRamsey.Partite.System L P X) (S : Set X) :
    (C.induce S).toRelStructure = C.toRelStructure.induce S := rfl

/-- The underlying relational structure of the pinned partite attachment
is definitionally the free relational attachment on exactly the same core,
standard indices, and actual vertices. -/
theorem track3_partiteAttachment_toRelStructure_eq
    (C : StructuralRamsey.Partite.System L P X) (S : Set X)
    (R : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) R) :
    (StructuralRamsey.Partite.Attachment.attach C S R f).toRelStructure =
      RelStructure.Attachment.attach C.toRelStructure S R.toRelStructure
        (fun i => (f i).toEmbedding) := rfl


/-- A genuine partite attachment has output A-linearity, every generated wagon
A-strong and all adjacent parameters, conditional only on the actual source
picture/cut geometry and the original lower witness full-system bounds.
The conclusion retains every actual A-support edge and every wagon label. -/
theorem track3_joint_geometry_and_parameters
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (e : RelStructure.Embedding A D)
    (active : StructuralRamsey.Partite.ProjectedEmbedding A C e.toFunctionEmbedding)
    (R : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) R)
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (U : EdgeTrainLevels (OldACarrierEdge A R.toRelStructure) m)
    (allowedParts : Fin (m + 1) → Set P)
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hm : 2 ≤ m)
    (hOldCut : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (selectedPictureOrderOneData A B D C family selected T μ).LinearPretrain)
    (hOldParams : T.AdjacentParameters
      (fun edge : OldACarrierEdge A C.toRelStructure => edge.1)
      (fun ν => {x | C.part x ∈ allowedParts ν}))
    (hCoreParams : U.AdjacentParameters
      (fun edge : OldACarrierEdge A R.toRelStructure => edge.1)
      (fun ν => {y | R.part y ∈ allowedParts ν}))
    (hInterior : ∀ κ : Fin (m + 1), 0 < κ.val → κ.val < m →
      ∀ (i : I) (s t : SharedOldACarrierEdge A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding)),
      T.rel κ
        (sharedOldACarrierInclusion A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) s)
        (sharedOldACarrierInclusion A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) t) ↔
      U.rel κ
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) R.toRelStructure
          (fun i => (f i).toEmbedding) i s)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) R.toRelStructure
          (fun i => (f i).toEmbedding) i t))
    (g : Fin (m + 1) → ℕ)
    (hg : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m → 2 ≤ g μ)
    (hCoreCut : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (activeGluingWitnessOrderOneData A C e.toFunctionEmbedding
        R.toRelStructure (fun i => (f i).toEmbedding) U μ).FullSystemGirthGT (g μ)) :
    let S := activeCarrier A C e.toFunctionEmbedding
    let fRel := fun i => (f i).toEmbedding
    let hShared := activeCarrier_all_standard_copies_meet_core
      A C e.toFunctionEmbedding active I
    let Train := generatedActualASupportTrain
      A hA C.toRelStructure S R.toRelStructure fRel T U hShared
    let Actual := RelStructure.Attachment.attach
      C.toRelStructure S R.toRelStructure fRel
    (ALinear A Actual ∧
      ∀ μ : Fin (m + 1),
        (attachedSelectedPictureOrderOneData A hA B D C family selected
          e R.toRelStructure fRel T U hShared μ).LinearPretrain ∧
        ∀ W : Quotient (Train.wagonSetoid μ),
          AStrong A Actual
            (Train.wagonClassCarrier
              (fun edge : OldACarrierEdge A Actual => edge.1) μ W)) ∧
    Train.AdjacentParameters
      (fun edge : ActualAttachedAEdge A C.toRelStructure S
        R.toRelStructure fRel => edge.1)
      (fun ν => {x |
        (StructuralRamsey.Partite.Attachment.attach C S R f).part x ∈ allowedParts ν}) := by
  have hGeo := attachedSelectedPicture_allLevels_linear_and_strong_of_two_le_height
    A hA B D C family selected e active R.toRelStructure
    (fun i => (f i).toEmbedding) T U hInterior
    hPartite hBaseLinear hRigid hm hOldCut g hg hCoreCut
  have hOrderOne : ∀ ν : Fin (m + 1), 0 < ν.val → ν.val < m →
      (sharedWitnessOrderOneData U ν
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) R.toRelStructure
          (fun i => (f i).toEmbedding))
        (fun edge : OldACarrierEdge A R.toRelStructure => edge.1)).Bound := by
    intro ν hPos hLt
    have hFull := hCoreCut ν hPos hLt
    rw [activeGluingWitnessOrderOneData_eq_shared
      A C e.toFunctionEmbedding R.toRelStructure
      (fun i => (f i).toEmbedding) U ν] at hFull
    exact OrderOneData.bound_of_fullSystemGirth_ge_one _ (g ν)
      (Nat.le_trans (by decide : 1 ≤ 2) (hg ν hPos hLt)) hFull
  -- The partite attachment is definitionally the same actual relational
  -- attachment used by hGeo; see track3_partiteAttachment_toRelStructure_eq.
  have hParams := activeAttached_actualASupport_allAdjacentParameters_of_intrinsic
    A hA C e.toFunctionEmbedding active R f T U allowedParts
    hOldParams hCoreParams hInterior hOrderOne
  exact ⟨hGeo, hParams⟩

end StructuralRamsey.Girth
