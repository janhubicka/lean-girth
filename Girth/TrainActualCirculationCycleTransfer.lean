import Girth.TrainActualOutputGirthFromOriginalTwo
import Girth.TrainActualBottomReducedTransfer

set_option autoImplicit false
set_option Elab.async false

/-!
# The cycle-transfer interface for the shortened circulation proof

The input is the genuine witness bound, or singleton witness wagons with
explicit reduction data: no cuts, a global supreme plan on the actual cut
cycle, or its mixed two-connector bridge alternative. The latter alternative
contains real core edges. No output supremeness callback is assumed.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualCirculationCycleTransfer

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
variable (hShared : ∀ _i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
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
local notation "CoreEdge" => OldACarrierEdge A R
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "ActualEdge" => OldACarrierEdge A
  (RelStructure.Attachment.attach C.toRelStructure S R f)
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Train" => generatedActualASupportTrain A hA
  C.toRelStructure S R f T U hShared
local notation "Std" => RelStructure.Attachment.copyEmbedding
  C.toRelStructure S R f
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

local notation "CoreActual" => (fun (b : CoreEdge) =>
  actualAPictureEdgeEquiv A hA C.toRelStructure S R f
    (physicalCoreEdge (sharedOldACarrierInclusion A C.toRelStructure S) I b))
local notation "CoreWagon" => generatedActualASupportTrain_coreWagonEmbedding
  A hA C.toRelStructure S R f T U
  (fun ν j p q h => Iff.mp (hRel ν j p q) h) hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- Physical transfer for the precise two alternatives used by the
circulation argument. The old bound and the source order budget use the
same cutoff. The singleton-wagon case uses only the displayed actual
reduced certificate or physical mixed bridges. -/
theorem attachedSelectedPicture_circulation_cycle_transfer
    [Finite UA]
    (q : ℕ) (hq : 2 ≤ q)
    (hLinear : (Out).LinearPretrain)
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n) (hAccept : K.Acceptable)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k, GeomAllowed (K.label k) (owner k))
    (hReduction : (Wit).FullSystemGirthGT q ∨
      (Function.Injective (Wit).parent ∧
        (cyclicOwnerChanges owner = 0 ∨
          ∃ hCuts : 2 ≤ cyclicOwnerChanges owner,
          let Z := attachedSelectedPicture_geometric_cutBigCycle
            A hA B D C family selected e R f T U hShared hRel μ
            K owner hAllowed hCuts
          Z.HasSimultaneousSupreme ∨
            ∃ (hTwo : cyclicOwnerChanges owner = 2)
              (x : Y) (p : Quotient (U.wagonSetoid μ)),
              ((Z.connector ⟨0, by omega⟩ = Sum.inl x ∧
                Z.connector ⟨1, by omega⟩ = Sum.inr p) ∨
               (Z.connector ⟨0, by omega⟩ = Sum.inr p ∧
                Z.connector ⟨1, by omega⟩ = Sum.inl x)) ∧
              ∀ k, (Wit).Bridge (Z.label k) x p))) :
    K.HasSimultaneousSupreme := by
  have hq1 : 1 ≤ q := by omega
  rcases hReduction with hWitness | ⟨hBottom, hData⟩
  · exact (attachedSelectedPicture_fullSystemGirth
      A hA B D C family selected e R f T U hShared hRel μ
      q hq1 hLinear hStrong hTwoCopies hOldStrong hCoreStrong
      hOldSupreme hWitness).2 n K hAccept hOrder
  · rcases hData with hZero | ⟨hCuts, hReduced | ⟨hTwo, x, p, hMixed, hBridges⟩⟩
    · exact attachedSelectedPicture_zero_cut_supreme_of_old_bound
        A hA B D C family selected e R f T U hShared hRel μ
        hStrong hTwoCopies hOldStrong hCoreStrong
        K hAccept hOldSupreme hOrder owner hAllowed hZero
    · exact attachedSelectedPicture_bottom_reduced_supreme
        A hA B D C family selected e R f T U hShared hRel μ
        q hq1 hStrong hTwoCopies hOldStrong hCoreStrong hOldSupreme
        K hAccept hLinear hOrder owner hAllowed hCuts hBottom hReduced
    · exact attachedSelectedPicture_bottom_mixed_bridges_supreme
        A hA B D C family selected e R f T U hShared hRel μ
        q hq1 hStrong hTwoCopies hOldStrong hCoreStrong hOldSupreme
        K hAccept hLinear hOrder owner hAllowed hTwo hBottom x p hMixed hBridges

end ActualCirculationCycleTransfer
end StructuralRamsey.Girth
