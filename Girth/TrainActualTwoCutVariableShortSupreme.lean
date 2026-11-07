import Girth.TrainActualTwoCutSingletonShortStandardTransfer
import Girth.TrainActualTwoCutShortSingletonOrientation
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: each two-cut target may use its OWN physical short edge

The source singleton argument needs only a valid reduced ShortValid
piece at EACH of the two possible chosen target standards. It does
NOT require one physical core A-edge to work for both targets.

Choose one reduced cut and one genuine short there to force a
forward singleton original owner run, using the verified source
A2/A3 two-contact theorem. Then choose the OTHER actual reduced
standard as target and its own (possibly different) valid short
piece at that singleton. The checked original-source one-short/
all-keep standard transfer proves full simultaneous supremeness
of the ORIGINAL acceptable cycle, with exact old cutoff.

This generalizes the shared-edge pair case and is also the right
input for the order-one vertex/wagon bridges: each designated
standard can have its own bridge edge in the same wagon through
the same vertex. It does not solve edge-only owner labels,
missing designated standards or long/no-pair physical transfers.
No appendix or circulation TeX edit.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutVariableShort

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
local notation "Selected" =>
  {r : DesignatedCopy B D C family // r ∈ selected}
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- Each reduced designated target can use a different real short
edge. This is sufficient for original-source global supremeness once
there are exactly two geometric owner cuts and the source has n>=3. -/
theorem attachedSelectedPicture_two_cut_variable_shorts_supreme
    [Finite UA]
    (hStrong : ∀ r : RelStructure.Embedding B D, r ∈ family →
      AStrong A D (copyCarrier r))
    (hTwoCopies : ∀ r : Selected, ∃ a c : OldEdge,
      a ≠ c ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        c.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    {n q : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hLinear : (Out).LinearPretrain)
    (hn : 3 ≤ n) (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwoCuts : cyclicOwnerChanges owner = 2)
    (hStandards : ∀ k : Fin (cyclicOwnerChanges owner),
      ∃ i : I, (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).label k = Sum.inl i)
    (hEachShort : ∀ cut : Fin (cyclicOwnerChanges owner),
      ∃ b : CoreEdge,
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).ShortValid Wit
          (trainCyclicPred cut) cut b)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let c0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  obtain ⟨b0, hShort0⟩ := hEachShort c0
  obtain ⟨singleton, hForward⟩ :=
    attachedSelectedPicture_two_cut_short_some_singleton_run
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hTwoCuts
      (trainCyclicPred c0) c0 b0 hShort0
  obtain ⟨i, hTarget⟩ := hStandards (trainCyclicPred singleton)
  obtain ⟨b, hShort⟩ := hEachShort singleton
  exact attachedSelectedPicture_two_cut_singleton_short_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwoCuts singleton hForward
    i hTarget b hShort hOldSupreme

end ActualTwoCutVariableShort
end StructuralRamsey.Girth
