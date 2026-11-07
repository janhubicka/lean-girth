import Girth.TrainActualTwoCutVariableShortSupreme
import Girth.TrainTwoMixedBridgeShortValidBoth
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: original source supreme from two distinct mixed bridge edges

This is the EXACTLY TWO geometric owner-cut, two-DESIGNATED-standard,
order-one vertex/wagon boundary case. The two reduced connectors
are one actual witness vertex x and one actual wagon p, in either
cyclic orientation. Each reduced standard label has its OWN real
bridge through x in p, as provided by the already checked witness
order-one bridge theorem.

Each chosen bridge yields a genuine reduced ShortValid, with the
OTHER standard selected as target. Source A2/A3 forces one original
owner run singleton; the singleton-complement theorem then chooses
the correct OTHER standard, regardless of orientation or different
physical bridge edges. The existing one-short/all-keep source
standard transfer proves FULL K.HasSimultaneousSupreme.

This does NOT assume a common bridge edge, a false original
designated-label identity, or a source-level global supreme plan.
It remains conditional on both reduced labels being designated
standards and on both physical bridge witnesses. The latter are
provided independently by FullSystemGirthGT at positive cutoff,
but edge-only reduced-label cases still need separate treatment.
No appendix or manuscript modifications.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutMixedBridges

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
local notation "Selected" => {r : DesignatedCopy B D C family // r ∈ selected}
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

/-- A two-cut selected output whose reduced vertex/wagon word is
fully supported by TWO designated standards has global original
simultaneous supremeness whenever each standard has its genuine
mixed physical bridge. Different bridge edges are allowed. -/
theorem attachedSelectedPicture_two_cut_mixed_bridges_full_supreme
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
    (x : Y) (p : Quotient (U.wagonSetoid μ))
    (hMixed :
      ((attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inl x ∧
       (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inr p) ∨
      ((attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨0, by omega⟩ = Sum.inr p ∧
       (attachedSelectedPicture_geometric_cutBigCycle
        A hA B D C family selected e R f T U hShared hRel μ
        K owner hAllowed (by omega)).connector ⟨1, by omega⟩ = Sum.inl x))
    (hBridges : ∀ k : Fin (cyclicOwnerChanges owner),
      (Wit).Bridge
        ((attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label k) x p)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    K.HasSimultaneousSupreme := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hEachShort : ∀ cut : Fin (cyclicOwnerChanges owner),
      ∃ b : CoreEdge, Z.ShortValid Wit (trainCyclicPred cut) cut b :=
    OrderOneData.BigCycle.two_mixed_bridges_shortValid_at_each_cut_of_two
      Wit hTwoCuts Z x p hMixed hBridges
  exact attachedSelectedPicture_two_cut_variable_shorts_supreme
    A hA B D C family selected e R f T U hShared hRel μ
    hStrong hTwoCopies hOldStrong hCoreStrong
    K hAccept hLinear hn hOrder
    owner hAllowed hTwoCuts hStandards hEachShort hOldSupreme

end ActualTwoCutMixedBridges
end StructuralRamsey.Girth
