import Girth.TrainActualBottomFullSystemForestPreservation
import Girth.TrainActualWitnessBottomMixedForestBridge
import Girth.TrainActiveGluingWitness

set_option autoImplicit false
set_option Elab.async false

/-!
# One-edge LOCAL active target: no two-source-edge assumption

For the single-edge local active target in the same-vector finite
conversion, the local forest requirement is trivial even if the
selected indexing lists the same one-edge support more than once.
All bottom support labels then have the same physical one-edge piece,
so their join tree can be any star. No source two-edge condition,
no injective support-family assumption and no F_t existence theorem
is required for this special local case.

The OLD target in the surrounding one-level preservation may still
have multiple A-support edges. The original B-labelled output
supreme plan is supplied by the full bottom preservation theorem.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v
section SingleEdgeLocalBottom

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
local notation "Actual" => RelStructure.Attachment.attach C.toRelStructure S R f
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μBottom
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "Local" => activeGluingWitnessOrderOneData
  A C e.toFunctionEmbedding R f U μBottom
local notation "Wit" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- At the actual bottom cut, the special LOCAL one-edge witness
is sufficient for original B-labelled full output system girth.
Unlike the general finite mixed-set adapter, it does not require
two distinct A-copies of the active source or distinct local images. -/
theorem attachedSelectedPicture_bottom_fullSystemGirth_of_singleEdgeLocal
    [Finite UA] [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hCoreLinear : ALinear A R)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoSelected : ∀ q : Selected,
      ∃ a b : OldEdge,
        a ≠ b ∧ a.1 ⊆ copyCarrier q.1.embedding ∧
          b.1 ⊆ copyCarrier q.1.embedding)
    (hActiveStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ i : I, AStrong A R (copyCarrier (f i)))
    (q : ℕ)
    (hOldSupreme : (Old).SupremeCycleBound q)
    (oneEdge : Set Y)
    (hAllCopies : ∀ i : I,
      bSupportPiece A (f i) = HypergraphPiece.oneEdge oneEdge)
    (hAllEdges : ∀ edge : CoreEdge, edge.1 = oneEdge) :
    (Out).FullSystemGirthGT q := by
  let HLocal : (Local).BottomForestGeometry :=
    activeGluingWitness_bottomForestGeometry
      A C e.toFunctionEmbedding R f U hCoreLinear
  have hLocalForest : LocalForestThrough
      ((Local).bottomForestPiece HLocal) q :=
    activeGluingWitness_bottom_localForest_of_singleEdge
      A C e.toFunctionEmbedding R f U HLocal
      oneEdge hAllCopies hAllEdges q
  have hEquality : Local = Wit :=
    activeGluingWitnessOrderOneData_eq_shared
      A C e.toFunctionEmbedding R f U μBottom
  have hWitnessForest :
      ∃ H : (Wit).BottomForestGeometry,
        LocalForestThrough ((Wit).bottomForestPiece H) q := by
    rw [← hEquality]
    exact ⟨HLocal, hLocalForest⟩
  obtain ⟨H, hLocal⟩ := hWitnessForest
  exact attachedSelectedPicture_bottom_fullSystemGirth_of_localForest
    A hA B D C family selected e R f T U hShared hRel
    hPhysical hStrong hTwoSelected hActiveStrong hCoreStrong
    H q hLocal hOldSupreme

end SingleEdgeLocalBottom
end StructuralRamsey.Girth
