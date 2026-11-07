import Girth.TrainActualTwoCutSingletonShortStandardTransfer
import Girth.TrainActualTwoCutShortSingletonOrientation
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: one physical edge that is ShortValid toward either standard

In an actual selected picture with EXACTLY TWO geometric owner cuts,
suppose the SAME real core support edge b is a valid reduced SHORT
piece from the other designated standard at BOTH cut indices.
This is precisely the symmetric short conclusion that witness
pair-edge ownership will supply at the two-vertex cut word.

First choose an arbitrary cut. Its physical ShortValid transfers
to the ORIGINAL source connectors, and source A2/A3 forces one
of the two owner runs to be a genuine singleton, in a unique
cyclic orientation for n>=3.

At THAT singleton cut, choose the OTHER reduced designated standard
as target, and use the already checked actual singleton source
short transfer. Every source position outside the singleton
keeps its original label and has the chosen standard as a genuine
geometric owner; all long-piece geometry and freshness conditions
are vacuous. The resulting conclusion is FULL original source
HasSimultaneousSupreme, not just local ShortValid.

This interface assumes symmetric ShortValid for the same actual edge
and designatedness of both reduced owner labels. It does not yet
derive them from witness FullSystemGirthGT; that is the separate
pair-edge ownership step. It makes no assumption about original
B-copy labels and performs no appendix/manuscript edit.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutSymmetricShort

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

/-- Symmetric actual ShortValid at BOTH two-cut indices is enough
to choose the correctly oriented singleton original run and get
FULL original-cycle simultaneous supremeness. No chosen reduced
global plan is postulated: we use a single physical b at both
possible reduced standard targets. -/
theorem attachedSelectedPicture_two_cut_symmetric_short_supreme
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
    (b : CoreEdge)
    (hEveryShort : ∀ k : Fin (cyclicOwnerChanges owner),
      (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).ShortValid Wit
        (trainCyclicPred k) k b)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let c0 : Fin (cyclicOwnerChanges owner) := ⟨0, by omega⟩
  obtain ⟨singleton, hForward⟩ :=
    attachedSelectedPicture_two_cut_short_some_singleton_run
      A hA B D C family selected e R f T U hShared hRel μ
      K hAccept owner hAllowed hTwoCuts
      (trainCyclicPred c0) c0 b (hEveryShort c0)
  obtain ⟨i, hTarget⟩ := hStandards (trainCyclicPred singleton)
  exact attachedSelectedPicture_two_cut_singleton_short_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwoCuts singleton hForward i hTarget
    b (hEveryShort singleton) hOldSupreme

end ActualTwoCutSymmetricShort
end StructuralRamsey.Girth
