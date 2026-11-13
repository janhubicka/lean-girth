import Girth.TrainActualBottomDesignatedBoundary
import Girth.TrainActualCutConnectorLift
import Girth.TrainCoreWagonEmbedding

set_option autoImplicit false
set_option Elab.async false

/-!
# A genuine bottom geometric owner cut lies in the shared core

The previously checked physical cut-connector lift gives an actual
core vertex or core wagon. At the bottom equality cut, a core wagon
contains exactly one physical edge. Any output edge with this parent
is THAT core edge, whose carrier lies in the core.

Both boundary orientations of an isolated segment are covered. This
discharges the remaining physical cut input of the bottom
no-mixed-singleton theorem without assuming output system girth,
a reduced supreme label, or an unconstructed local witness.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section ActualBottomCutGeometry

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
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "ActualEdge" => OldACarrierEdge A Actual
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Std" => RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "Core" => RelStructure.Attachment.coreEmbedding C.toRelStructure S R f
local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "Train" => generatedActualASupportTrain
  A hA C.toRelStructure S R f T U hShared
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom
local notation "CoreWagon" =>
  generatedActualASupportTrain_coreWagonEmbedding
    A hA C.toRelStructure S R f T U
      (fun ν j p q h => (hRel ν j p q).mp h)
      hShared μBottom

/-- Any bottom output edge with the same wagon as one true core edge
is that core edge, and is therefore wholly carried by the shared core.
This uses bottom-parent injectivity, not an artificial edge restriction. -/
theorem attachedSelectedPicture_bottom_sameCoreWagon_carrier
    (H : (Out).BottomForestGeometry)
    (b : CoreEdge) (a : ActualEdge)
    (hParent : (Out).parent a = (Out).parent (CoreActual b)) :
    a.1 ⊆ copyCarrier Core := by
  have hEq : a = CoreActual b := H.parent_injective hParent
  subst a
  rw [actualAPictureEdgeEquiv_core_carrier
    A hA C.toRelStructure S R f b]
  change ((fun y : Y => Core y) '' b.1) ⊆ copyCarrier Core
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, rfl⟩

include hRel

/-- Classify the exact connector of a genuine geometric owner change:
it is either an actual core vertex or the bottom wagon of an actual
core edge. This retains the original output connector, not a shadow. -/
theorem attachedSelectedPicture_bottom_cut_connector_core
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (k : Fin n)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (∃ y : Y, K.connector k = Sum.inl (Core y)) ∨
      (∃ b : CoreEdge,
        K.connector k = Sum.inr ((Out).parent (CoreActual b))) := by
  obtain ⟨q, hMap⟩ :=
    attachedSelectedPicture_geometric_cut_connector_lift
      A hA B D C family selected e R f T U hShared hRel μBottom
      K owner hAllowed k hCut
  cases q with
  | inl y =>
      left
      refine ⟨y, ?_⟩
      simpa only [Sum.map_inl] using hMap.symm
  | inr w =>
      induction w using Quotient.inductionOn with
      | h b =>
          right
          refine ⟨b, ?_⟩
          have hb :
              (Out).parent (CoreActual b) =
                CoreWagon (Quotient.mk (U.wagonSetoid μBottom) b) :=
            (generatedActualASupportTrain_coreWagonEmbedding_mk
              A hA C.toRelStructure S R f T U
              (fun ν j p q h => (hRel ν j p q).mp h)
              hShared μBottom b).symm
          change Sum.inr (CoreWagon
            (Quotient.mk (U.wagonSetoid μBottom) b)) = K.connector k at hMap
          rw [← hb] at hMap
          exact hMap.symm

/-- At every genuine owner cut, its vertex belongs to the shared core;
alternatively, the whole bottom wagon edge lies in the core. The two
conclusions have precisely the connector kinds needed for the
mixed-singleton argument, including cyclic wrap. -/
theorem attachedSelectedPicture_bottom_cut_connector_core_geometry
    (H : (Out).BottomForestGeometry)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (k : Fin n)
    (hCut : owner k ≠ owner (cyclicSucc k)) :
    (∀ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      K.connector k = Sum.inl x → x ∈ copyCarrier Core) ∧
    (∀ p : Quotient ((Train).wagonSetoid μBottom),
      K.connector k = Sum.inr p →
      ∀ a : ActualEdge, (Out).parent a = p →
        a.1 ⊆ copyCarrier Core) := by
  have hClass := attachedSelectedPicture_bottom_cut_connector_core
    A hA B D C family selected e R f T U hShared hRel
    K owner hAllowed k hCut
  constructor
  · intro x hx
    rcases hClass with ⟨y, hy⟩ | ⟨b, hb⟩
    · have heq : Core y = x := Sum.inl.inj (hy.symm.trans hx)
      exact ⟨y, heq⟩
    · cases (hb.symm.trans hx)
  · intro p hp a ha
    rcases hClass with ⟨y, hy⟩ | ⟨b, hb⟩
    · cases (hy.symm.trans hp)
    · have hbp : (Out).parent (CoreActual b) = p :=
        Sum.inr.inj (hb.symm.trans hp)
      exact attachedSelectedPicture_bottom_sameCoreWagon_carrier
        A hA B D C family selected e R f T U hShared
        H b a (ha.trans hbp.symm)

/-- The two cut connectors surrounding any isolated mixed segment
have their actual physical core geometry. No abstract reduction
connector is silently substituted for the original one. -/
theorem attachedSelectedPicture_bottom_mixed_singleton_cut_core
    (H : (Out).BottomForestGeometry)
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hMixed :
      ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      ∃ p : Quotient ((Train).wagonSetoid μBottom),
        (K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
        (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) :
    ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
    ∃ p : Quotient ((Train).wagonSetoid μBottom),
      ((K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
       (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) ∧
      x ∈ copyCarrier Core ∧
      (∀ a : ActualEdge, (Out).parent a = p →
        a.1 ⊆ copyCarrier Core) := by
  have hPrevCut : owner (trainCyclicPred k) ≠
      owner (cyclicSucc (trainCyclicPred k)) := by
    simpa only [cyclicSucc_trainCyclicPred_of_two_le K.length_ge_two k]
      using hLeftCut
  obtain ⟨hPrevVertex, hPrevWagon⟩ :=
    attachedSelectedPicture_bottom_cut_connector_core_geometry
      A hA B D C family selected e R f T U hShared hRel
      H K owner hAllowed (trainCyclicPred k) hPrevCut
  obtain ⟨hHereVertex, hHereWagon⟩ :=
    attachedSelectedPicture_bottom_cut_connector_core_geometry
      A hA B D C family selected e R f T U hShared hRel
      H K owner hAllowed k hRightCut
  obtain ⟨x, p, hKinds⟩ := hMixed
  rcases hKinds with ⟨hPrev, hHere⟩ | ⟨hPrev, hHere⟩
  · exact ⟨x, p, Or.inl ⟨hPrev, hHere⟩,
      hPrevVertex x hPrev, hHereWagon p hHere⟩
  · exact ⟨x, p, Or.inr ⟨hPrev, hHere⟩,
      hHereVertex x hHere, hPrevWagon p hPrev⟩

/-- Full actual mixed-singleton exclusion, with only the standard
old/attached geometry: ordinary output A-linearity, strongly induced
base B-projections, exact shared train restriction and genuine
minimal geometric owner choice. No local forest/girth oracle appears. -/
theorem attachedSelectedPicture_bottom_normalized_minimal_no_mixed_singleton
    [Nontrivial UA]
    (hLinear : ALinear A Actual)
    (hStrong : ∀ q : Selected, AStrong A D (copyCarrier q.1.base))
    {n : ℕ} (K : (Out).BigCycle n)
    (hNormalized : K.MixedNormalized Out)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hMinimal : ∀ other : Fin n → I ⊕ CoreEdge,
      (∀ j, GeomAllowed (K.label j) (other j)) →
      cyclicOwnerChanges owner ≤ cyclicOwnerChanges other)
    (k : Fin n)
    (hLeftCut : owner (trainCyclicPred k) ≠ owner k)
    (hRightCut : owner k ≠ owner (cyclicSucc k))
    (hMixed :
      ∃ x : RelStructure.Attachment.Vertex S (W := Y) (I := I),
      ∃ p : Quotient ((Train).wagonSetoid μBottom),
        (K.connector (trainCyclicPred k) = Sum.inl x ∧
          K.connector k = Sum.inr p) ∨
        (K.connector (trainCyclicPred k) = Sum.inr p ∧
          K.connector k = Sum.inl x)) : False := by
  let H := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hLinear
  have hCoreMixed :=
    attachedSelectedPicture_bottom_mixed_singleton_cut_core
      A hA B D C family selected e R f T U hShared hRel
      H K owner hAllowed k hLeftCut hRightCut hMixed
  exact attachedSelectedPicture_bottom_no_mixed_singleton_of_base_strong
    A hA B D C family selected e R f T U hShared
    hLinear hStrong K hNormalized owner hAllowed hMinimal
    k hLeftCut hRightCut hCoreMixed

end ActualBottomCutGeometry

end StructuralRamsey.Girth
