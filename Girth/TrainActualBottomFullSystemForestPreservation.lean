import Girth.TrainActualBottomAtLeastThreeForestPreservation
import Girth.TrainActualBottomOriginalTwoCycleAll
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# ACTUAL one-step bottom forest -> full original system-girth

At the bottom equality cut, all original acceptable source BigCycles
with order at most q have a genuine ORIGINAL designated B supreme copy:

* Original source n=2: equal geometric owner => old one-standard
  system bound; distinct geometric owners => directly allowed full-core
  intersection, so the two-member forest theorem supplies an original
  designated supreme plan. No lower witness girth certificate needed.
* Original source n>=3: simultaneous short normalization, true minimum
  geometric owners, the DIRECT cyclic owner-cut budget, and the already
  existing physical one-pass original-copy transfers for 0, 2, >=3
  cut runs. Only the local selected mixed-forest bound is used.

Output bottom LinearPretrain follows from genuine physical A-linearity
and injectivity of the equality-cut wagon parent. The full system
certificate keeps ALL original selected B-labels, physical A-edges,
quotient wagon labels and original source connectors.

This is conditional on an ACTUAL selected local witness whose
bottom forest property is given; constructing that witness from
the Ramsey forest assertion F_t belongs to the finite conversion.
No full local witness system-girth premise is smuggled in.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section BottomFullSystemForestPreservation

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "μBottom" => (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μBottom
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μBottom
local notation "Wit" => sharedWitnessOrderOneData U μBottom
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- The full bottom one-step circulation system-girth preservation
theorem, for ALL source lengths n>=2 and original B-designations.
Local forest, not full witness system-girth, is the only local Ramsey
input. The local forest itself remains an explicit actual input. -/
theorem attachedSelectedPicture_bottom_fullSystemGirth_of_localForest
    [Finite UA] [Nontrivial UA]
    (hPhysical : ALinear A Actual)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwoCopies : ∀ r : Selected, ∃ a b : OldEdge,
      a ≠ b ∧ a.1 ⊆ copyCarrier r.1.embedding ∧
        b.1 ⊆ copyCarrier r.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (H : (Wit).BottomForestGeometry)
    (q : ℕ)
    (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    (hOldSupreme : (Old).SupremeCycleBound q) :
    (Out).FullSystemGirthGT q := by
  let HOut := attachedSelectedPicture_bottomForestGeometry
    A hA B D C family selected e R f T U hShared hPhysical
  have hLinear : (Out).LinearPretrain :=
    OrderOneData.BottomForestGeometry.linearPretrain Out HOut
  refine ⟨hLinear, ?_⟩
  intro n K hAccept hOrder
  by_cases hn2 : n = 2
  · subst n
    exact attachedSelectedPicture_bottom_two_cycle_supreme
      A hA B D C family selected e R f T U hShared hRel
      hPhysical hStrong hTwoCopies hOldStrong hCoreStrong
      q hOldSupreme K hAccept hOrder
  · have hn3 : 3 ≤ n := by
      have hnMin := K.length_ge_two
      omega
    exact attachedSelectedPicture_bottom_supreme_three_le_of_localForest
      A hA B D C family selected e R f T U hShared hRel
      hPhysical hStrong hTwoCopies hOldStrong hCoreStrong
      H q hLocal hOldSupreme K hAccept hn3 hOrder

end BottomFullSystemForestPreservation
end StructuralRamsey.Girth
