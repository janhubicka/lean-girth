import Girth.TrainActualBottomForestReducedSupreme
import Girth.TrainActualThreeCutOnePassSupreme

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual bottom THREE-OR-MORE-CUT transfer from a mixed forest witness

The general three-cut physical source theorem already needs only one
genuine globally supreme plan of the ACTUAL reduced witness BigCycle.
It does NOT need full witness system girth after that plan is found.

At the bottom, a local forest through q and the direct cut budget
produce exactly such a plan (including the repeated-label details).
Reuse the checked standard-contained physical one-pass transfer,
recovering a supreme ORIGINAL selected B-copy of the source cycle.
This closes the >=3-cuts branch conditionally on the real local
forest witness and the usual old-picture geometric premises.
It does not claim the two-cut/source length-two branch.
-/

namespace StructuralRamsey.Girth
open StructuralRamsey.RelStructure

universe u v

section BottomThreeCut

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
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μBottom

include hRel

/-- Genuine three-or-more-cut bottom transfer, using only local
mixed forests in place of a full witness system-girth hypothesis.
The source's selected-copy supreme label and all physical edges
remain unchanged by the existing one-pass transfer. -/
theorem attachedSelectedPicture_bottom_three_cut_supreme_of_localForest
    [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    (hOldStrong : AStrong A C.toRelStructure S)
    (hCoreStrong : ∀ j : I, AStrong A R (copyCarrier (f j)))
    (hOutputLinear : (Out).LinearPretrain)
    (H : (Wit).BottomForestGeometry)
    (q : ℕ)
    (hLocal : LocalForestThrough ((Wit).bottomForestPiece H) q)
    (hOldSupreme : (Old).SupremeCycleBound q)
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable) (hn : 3 ≤ n)
    (hOrder : K.twiceOrder ≤ 2 * q)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hThree : 3 ≤ cyclicOwnerChanges owner)
    (hBudget : cyclicOwnerChanges owner ≤ q) :
    K.HasSimultaneousSupreme := by
  have hCuts : 2 ≤ cyclicOwnerChanges owner := by omega
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μBottom
    K owner hAllowed hCuts
  have hReduced : Z.HasSimultaneousSupreme :=
    attachedSelectedPicture_bottom_reduced_supreme_of_localForest
      A hA B D C family selected e R f T U hShared hRel
      H q hLocal K owner hAllowed hCuts hBudget
      hAccept.2.1 hAccept.2.2
  obtain ⟨target, hDesignated, pieces, hPlan, hProduces⟩ := hReduced
  have hLabel : ∃ i : I, Z.label target = Sum.inl i := by
    cases h : Z.label target with
    | inl i =>
        exact ⟨i, h⟩
    | inr b =>
        have hImpossible : False := by
          have hCopy := hDesignated
          rw [h] at hCopy
          exact hCopy
        exact False.elim hImpossible
  obtain ⟨i, hTarget⟩ := hLabel
  have hSupremeAt : Z.HasSupremeAt Wit target :=
    ⟨hDesignated, pieces, hPlan, hProduces⟩
  exact attachedSelectedPicture_three_cut_one_pass_supreme_of_old_bound
    A hA B D C family selected e R f T U hShared hRel μBottom
    hStrong hTwo hOldStrong hCoreStrong
    K hAccept hOutputLinear hn hOrder owner hAllowed hThree
    target i hTarget hSupremeAt hOldSupreme

end BottomThreeCut
end StructuralRamsey.Girth
