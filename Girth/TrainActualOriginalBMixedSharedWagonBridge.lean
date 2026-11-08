import Girth.TrainOriginalCopyProbePhysicalMap
import Girth.TrainRealSharedLongOldWagonProbe
import Girth.TrainActualStandardPhysicalMap
import Girth.TrainCoreWagonBridge
import Girth.TrainSelectedPictureOutputIncidence
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# The real witness bridge yields a SHORT in the ORIGINAL selected B-copy

At original source length two with mixed vertex/wagon boundaries
the reduced lower witness supplies a bridge through its true
core vertex x in its true core wagon w, belonging to genuine
lower gluing copy i. This bridge is NOT an edge of the
original selected B-copy q.

The actual original B-copy (i,q) also genuinely MEETS the
output wagon W. Exact selected-output incidence supplies an
owned old A-edge r of q whose physical standard image has
original output parent W. The lower bridge gives a real shared
old A-edge s through the exact old vertex x0. Exact old/target
train reflection and the physical core-wagon embedding identify
the actual output parent of s with W. Injectivity of the
standard's wagon embedding therefore proves s and r have
the same OLD wagon parent; the OLD order-one supreme bound
constructs a genuinely owned original-q short edge through x0
in that wagon.

The verified actual standard LiteralPhysicalMap transports
that OWNED original-q short to the actual output endpoints.
We neither identify q with i nor construct a new output wagon
nor assume the output SupremeCycleBound.

The given LOWER bridge is a real piece hypothesis here;
deriving it from the two-cut reduced witness FullSystemGirthGT
and exact cut connector orientation is a separate final step.
No appendix.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section OriginalBMixedSelectedWagonBridge

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L VB) (D : RelStructure L P)
variable (C : StructuralRamsey.Partite.System L P X)
variable (family : Set (Embedding B D))
variable (selected : Set (DesignatedCopy B D C family))
variable (e : Embedding A D) (R : RelStructure L Y)
variable (f : I → Embedding
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
variable (μ : Fin (m + 1))

local notation "S" => activeCarrier A C e.toFunctionEmbedding
local notation "Selected" =>
  {q : DesignatedCopy B D C family // q ∈ selected}
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Shared" => SharedOldACarrierEdge A C.toRelStructure S
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "CoreEmb" => RelStructure.Attachment.coreEmbedding
  C.toRelStructure S R f
local notation "Emb" => sharedOldACarrierCoreEmbedding
  A C.toRelStructure S R f
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q hp => (hRel ν j p q).mp hp) hShared μ
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "StdEdge" => (fun (i : I) (old : OldEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalStandardEdge
      (sharedOldACarrierInclusion A C.toRelStructure S) Emb i old))
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  Emb (Subtype.val : CoreEdge → Set Y)

include hRel

/-- TRUE original selected B-labelled short replacement at a mixed
CORE vertex/output WAGON connector, from old source SupremeCycleBound
and a LOWER gluing-copy bridge whose genuine core wagon embeds into
that output wagon. The original selected label retains all its
physical edges, parent classes and source index. -/
theorem attachedSelectedPicture_original_B_mixed_short_of_lower_bridge
    {qcut : ℕ} (hq : 1 ≤ qcut)
    (hOld : (Old).SupremeCycleBound qcut)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (i : I) (q : Selected)
    (x0 : X) (x : Y)
    (hQX : x0 ∈ (Old).copyCarrier q)
    (hX : Std i x0 = CoreEmb x)
    (W : Quotient ((Train).wagonSetoid μ))
    (p : Quotient (U.wagonSetoid μ))
    (hWagon : CoreWagon p = W)
    (hOriginalWagon : (Out).Meets (Sum.inl (i, q)) W)
    (hWitnessBridge : (Wit).Bridge (Sum.inl i) x p) :
    (Out).ShortPiece (Sum.inl (i, q))
      (Sum.inl (CoreEmb x)) (Sum.inr W) := by
  obtain ⟨s, hsX, hsParent⟩ :=
    sharedWitness_bridge_old_vertex_wagon_probe
      A B D C family selected e R f T U μ
      i x0 x hX p hWitnessBridge
  obtain ⟨r, hrOwn, hrParent⟩ :=
    (attachedSelectedPicture_meets_iff
      A hA B D C family selected e R f T U hShared μ
      i (Sum.inl q) W).mp hOriginalWagon
  have hSelf : T.rel μ s.1 s.1 :=
    (T.equivalent μ).refl _
  have hStdCoreParent :
      (Out).parent (StdEdge i s.1) =
        CoreWagon (Quotient.mk (U.wagonSetoid μ) (Emb i s)) :=
    generatedActualASupportTrain_standard_wagon_eq_coreEmbedding
      A hA C.toRelStructure S R f T U hShared hRel μ
      i s.1 s hSelf
  have hSame : (Out).parent (StdEdge i s.1) =
      (Out).parent (StdEdge i r) := by
    calc
      (Out).parent (StdEdge i s.1) =
          CoreWagon (Quotient.mk (U.wagonSetoid μ) (Emb i s)) :=
        hStdCoreParent
      _ = CoreWagon p := congrArg CoreWagon hsParent
      _ = W := hWagon
      _ = (Out).parent (StdEdge i r) := hrParent.symm
  let M := attachedSelectedPicture_standard_physicalMap
    A hA B D C family selected e R f T U hShared hRel μ
    hOldStrong hCoreStrong i
  have hOldOwned : r ∈ (Old).copyEdges q := hrOwn
  have hShort :=
    M.original_copy_short_map_of_shared_wagon_contact
      hq hOld q x0 s.1 r hQX hOldOwned hsX hSame
  have hMappedLabel :
      M.mapLabel (Sum.inl q) = (Sum.inl (i, q) :
        (I × Selected) ⊕
          OldACarrierEdge A
            (RelStructure.Attachment.attach C.toRelStructure S R f)) := by
    rfl
  have hMappedX :
      M.mapConnector (Sum.inl x0) = Sum.inl (CoreEmb x) := by
    change Sum.inl (Std i x0) = Sum.inl (CoreEmb x)
    rw [hX]
  have hMappedW :
      M.mapConnector (Sum.inr ((Old).parent r)) = Sum.inr W := by
    change Sum.inr (StdWagon i ((Old).parent r)) = Sum.inr W
    have hStdWagon :
        StdWagon i ((Old).parent r) =
          (Out).parent (StdEdge i r) := by
      change StdWagon i (Quotient.mk (T.wagonSetoid μ) r) =
        Quotient.mk ((Train).wagonSetoid μ) (StdEdge i r)
      exact (generatedActualASupportTrain_standardWagonEmbedding_mk
        A hA C.toRelStructure S R f T U hRel hShared μ i r).symm
    rw [hStdWagon, hrParent]
  rw [hMappedLabel, hMappedX, hMappedW] at hShort
  exact hShort

end OriginalBMixedSelectedWagonBridge
end StructuralRamsey.Girth
