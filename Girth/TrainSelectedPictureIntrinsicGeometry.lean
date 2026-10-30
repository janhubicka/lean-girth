import Girth.TrainSelectedPictureLinearPretrain
import Girth.TrainVertexImageSystemGirth
import Girth.TrainEndpointGeometry
import Girth.TrainActiveGluingWitness
import Girth.TrainFullGirthCopyStrongness
import Girth.TrainActualActiveSharedEdge
import Girth.TrainSharedSupportInteriorCompatibility
import Girth.ActiveCarrierStrong

set_option Elab.async false

/-!
# Generated output geometry from intrinsic picture-step data

The induction supplies the old picture and local witness on their original
vertex types.  The generated-wagon theorems instead use the core's physical
image in the attachment and full shared-train compatibility.  This module
discharges that difference: an inhabited projected fibre supplies genuine
shared support, bottom equality and top universality supply endpoint
compatibility, and injective vertex transport supplies the attached-core
order-two hypothesis.  Base A-linearity and rigidity supply strongness of
the true active subsystem.

Only interior cuts need a witness cycle bound.  At the bottom, a wagon is
one actual support edge; at the top, it is the union of all actual support
edges.  These facts prove both endpoint linearity and strongness directly.
No support coverage, nonempty vertex type, fictitious core edge, or top
cycle coordinate is introduced.

The local witness's full order-two bound also gives strongness of its
whole gluing images.  Thus the single-cut interface and the all-level
interface for height at least two need no separate image-strongness input.
The general all-level interface retains that input to cover trains with
no interior cut.  Output system-girth and recursive witness existence are
not asserted here.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v

section IntrinsicGeometry

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (RelStructure.Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : RelStructure.Embedding A D)
variable (active : StructuralRamsey.Partite.ProjectedEmbedding A C e.toFunctionEmbedding)
variable (R : RelStructure L Y)
variable (f : I → RelStructure.Embedding
  (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
variable {m : ℕ}
variable (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
variable (U : EdgeTrainLevels (OldACarrierEdge A R) m)
variable (hInterior : ∀ (ν : Fin (m + 1)), 0 < ν.val → ν.val < m →
  ∀ (i : I) (p q : SharedOldACarrierEdge A C.toRelStructure
    (activeCarrier A C e.toFunctionEmbedding)),
  T.rel ν p.1 q.1 ↔
    U.rel ν
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f i p)
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f i q))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Emb" => sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
local notation "hShared" =>
  activeCarrier_all_standard_copies_meet_core A C e.toFunctionEmbedding active I
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "Old" => (fun ν : Fin (m + 1) =>
  selectedPictureOrderOneData A B D C family selected T ν)
local notation "Witness" => (fun ν : Fin (m + 1) =>
  activeGluingWitnessOrderOneData A C e.toFunctionEmbedding R f U ν)
local notation "Out" => (fun ν : Fin (m + 1) =>
  attachedSelectedPictureOrderOneData
    A hA B D C family selected e R f T U hShared ν)

include hInterior

/-- Intrinsic source data provide all of the auxiliary geometric inputs
to the checked generated-wagon theorem.  The order-two bound is obtained
from the actual local witness's full bound, not from output linearity. -/
theorem attachedSelectedPicture_linear_and_strong_of_intrinsic
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (μ : Fin (m + 1)) (hOld : (Old μ).LinearPretrain)
    (q : ℕ) (hq : 2 ≤ q) (hCore : (Witness μ).FullSystemGirthGT q) :
    (Out μ).LinearPretrain ∧
      ∀ W : Quotient ((Train).wagonSetoid μ),
        AStrong A Actual
          ((Train).wagonClassCarrier (fun edge : ActualEdge => edge.1) μ W) := by
  have hRel : ∀ (ν : Fin (m + 1)) (i : I) (p q : Shared),
      T.rel ν p.1 q.1 ↔ U.rel ν (Emb i p) (Emb i q) := by
    apply sharedSupportTrainRel_of_interior T U
      (sharedOldACarrierInclusion A C.toRelStructure S) Emb
    intro ν hZero hTop i p q
    exact hInterior ν (by omega) (by omega) i p q
  have hActive : AStrong A C.toRelStructure S :=
    activeCarrier_aStrong_of_base_aLinear
      A D C hA hPartite hBaseLinear e hRigid
  have hImage : ∀ i : I, AStrong A R (copyCarrier (f i)) :=
    activeGluingWitness_images_aStrong_of_fullSystemGirth
      A C e.toFunctionEmbedding R f U μ q hq hCore
  let core := RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
  have hCoreShared : (sharedWitnessOrderOneData U μ Emb
      (fun edge : OldACarrierEdge A R => edge.1)).FullSystemGirthGT q := by
    rw [← activeGluingWitnessOrderOneData_eq_shared A C e.toFunctionEmbedding R f U μ]
    exact hCore
  have hCoreImage : (sharedWitnessOrderOneData U μ Emb
      (attachedCoreAEdgeCarrier A C.toRelStructure S R f)).FullSystemGirthGT q :=
    sharedWitnessOrderOneData_fullSystemGirth_vertexImage U μ Emb
      (fun edge : OldACarrierEdge A R => edge.1)
      core.toFunctionEmbedding hCoreShared
  have hLocal : (sharedWitnessOrderOneData U μ Emb
      (attachedCoreAEdgeCarrier A C.toRelStructure S R f)).LocalPieceSystemBound 2 := by
    intro n K hAccept hOrder
    exact (sharedWitnessOrderOneData U μ Emb
      (attachedCoreAEdgeCarrier A C.toRelStructure S R f)).localPieceSystemBound_of_supremeCycleBound
        q hCoreImage.2 n K hAccept
        (hOrder.trans (Nat.mul_le_mul_left 2 hq))
  exact attachedSelectedPicture_linear_and_strong_of_gluing_geometry
    A hA B D C family selected e R f T U hShared μ hRel
    hOld hCoreImage.1 hLocal hActive hImage

/-- Every cut of the actual generated train is linear and every complete
generated wagon is A-strong.  The only cycle assumptions are the intrinsic
local witness bounds at strictly interior cuts.  Source physical
A-linearity also covers the case with no interior cuts. -/
theorem attachedSelectedPicture_allLevels_linear_and_strong_of_intrinsic
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hOldLinear : ALinear A C.toRelStructure) (hCoreLinear : ALinear A R)
    (hOldCut : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Old μ).LinearPretrain)
    (g : Fin (m + 1) → ℕ)
    (hg : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m → 2 ≤ g μ)
    (hCoreCut : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Witness μ).FullSystemGirthGT (g μ))
    (hImage : ∀ i : I, AStrong A R (copyCarrier (f i))) :
    ALinear A Actual ∧
      ∀ μ : Fin (m + 1), (Out μ).LinearPretrain ∧
        ∀ W : Quotient ((Train).wagonSetoid μ),
          AStrong A Actual
            ((Train).wagonClassCarrier (fun edge : ActualEdge => edge.1) μ W) := by
  have hActive : AStrong A C.toRelStructure S :=
    activeCarrier_aStrong_of_base_aLinear
      A D C hA hPartite hBaseLinear e hRigid
  have hLinear : ALinear A Actual :=
    attachment_aLinear C.toRelStructure S R f hA
      hOldLinear hCoreLinear hActive hImage
  have hEdges : ∀ a b : ActualEdge, a ≠ b →
      (a.1 ∩ b.1).Subsingleton :=
    oldACarrier_edges_inter_subsingleton_of_aLinear A Actual hLinear
  refine ⟨hLinear, ?_⟩
  intro μ
  by_cases hZero : μ.val = 0
  · have hμ : μ = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hZero
    subst μ
    exact ⟨(Out ⟨0, Nat.zero_lt_succ m⟩).linearPretrain_of_injective_parent
        hEdges (Train).bottom_parent_injective,
      actualASupport_bottom_wagon_aStrong A Actual (Train) hLinear⟩
  by_cases hTop : μ.val = m
  · have hμ : μ = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hTop
    subst μ
    exact ⟨(Out ⟨m, Nat.lt_succ_self m⟩).linearPretrain_of_constant_parent
        hEdges (Train).top_parent_eq,
      actualASupport_top_wagon_aStrong A Actual (Train)⟩
  have hPos : 0 < μ.val := by omega
  have hLt : μ.val < m := by omega
  exact attachedSelectedPicture_linear_and_strong_of_intrinsic
    A hA B D C family selected e active R f T U hInterior
    hPartite hBaseLinear hRigid μ (hOldCut μ hPos hLt)
    (g μ) (hg μ hPos hLt) (hCoreCut μ hPos hLt)

/-- At height at least two there is a genuine interior cut.  The old
and local bounds there supply both source physical linearity and
strongness of every whole gluing image.  No separate source-linearity
or image-strongness input, and no endpoint bound, is introduced. -/
theorem attachedSelectedPicture_allLevels_linear_and_strong_of_two_le_height
    (hPartite : C.IsPartiteOver D) (hBaseLinear : ALinear A D)
    (hRigid : ∀ b : RelStructure.Embedding A D, SameCopy b e → b = e)
    (hm : 2 ≤ m)
    (hOldCut : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Old μ).LinearPretrain)
    (g : Fin (m + 1) → ℕ)
    (hg : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m → 2 ≤ g μ)
    (hCoreCut : ∀ μ : Fin (m + 1), 0 < μ.val → μ.val < m →
      (Witness μ).FullSystemGirthGT (g μ)) :
    ALinear A Actual ∧
      ∀ μ : Fin (m + 1), (Out μ).LinearPretrain ∧
        ∀ W : Quotient ((Train).wagonSetoid μ),
          AStrong A Actual
            ((Train).wagonClassCarrier (fun edge : ActualEdge => edge.1) μ W) := by
  let μ : Fin (m + 1) := ⟨1, by omega⟩
  have hPos : 0 < μ.val := by simp [μ]
  have hLt : μ.val < m := by dsimp [μ]; omega
  have hOldLinear : ALinear A C.toRelStructure :=
    aLinear_of_oldACarrier_edges_inter_subsingleton A C.toRelStructure
      (hOldCut μ hPos hLt).1
  have hCoreLinear : ALinear A R :=
    aLinear_of_oldACarrier_edges_inter_subsingleton A R
      (hCoreCut μ hPos hLt).1.1
  have hImage : ∀ i : I, AStrong A R (copyCarrier (f i)) :=
    activeGluingWitness_images_aStrong_of_fullSystemGirth
      A C e.toFunctionEmbedding R f U μ (g μ) (hg μ hPos hLt)
      (hCoreCut μ hPos hLt)
  exact attachedSelectedPicture_allLevels_linear_and_strong_of_intrinsic
    A hA B D C family selected e active R f T U hInterior
    hPartite hBaseLinear hRigid hOldLinear hCoreLinear hOldCut
    g hg hCoreCut hImage

end IntrinsicGeometry

end StructuralRamsey.Girth
