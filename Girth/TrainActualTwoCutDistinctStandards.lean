import Girth.TrainActualPositiveCutTwoCutRankGate
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Path A: the two-cut all-designated case has exactly TWO distinct standards

When the actual positive-cut owner word has precisely two changes,
the predecessor and successor of any reduced occurrence are the SAME
other reduced occurrence. The designated-neighbor alternative in the
checked rank trichotomy therefore names one and the same genuine
gluing standard on both sides of the selected supreme standard.

The other index is different, and the BigCycle adjacency condition
forces the two standard indices themselves to differ. This does not
identify the original B-labels of the source cycle with those
standards, construct a source replacement, or prove the order-one
bridge case. This is a precise two-owner physical interface only.
No appendix or manuscript modifications.
-/

namespace StructuralRamsey.Girth

/-- Cyclic predecessor and successor coincide when the underlying
finite index set has exactly two elements. -/
theorem trainCyclicPred_eq_cyclicSucc_of_card_two
    {n : ℕ} (hn : n = 2) (j : Fin n) :
    trainCyclicPred j = cyclicSucc j := by
  subst n
  exact OrderOneData.finTwo_pred_eq_succ j

open StructuralRamsey.RelStructure

universe u v
section ActualTwoCutStandards

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
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ
local notation "Wit" => sharedWitnessOrderOneData U μ
  (sharedOldACarrierCoreEmbedding A C.toRelStructure S R f)
  (Subtype.val : CoreEdge → Set Y)

include hRel

/-- The names of the two designated neighboring standards in the
two-cut residual are equal, and this OTHER standard differs from the
selected one. Both conclusions use actual reduced labels; there is
no claim about the source's original designated B-copy labels. -/
theorem attachedSelectedPicture_two_cut_designated_neighbors_eq_distinct
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (target : Fin (cyclicOwnerChanges owner)) (i before after : I)
    (hTarget : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label target = Sum.inl i)
    (hBefore : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label (trainCyclicPred target) =
        Sum.inl before)
    (hAfter : (attachedSelectedPicture_geometric_cutBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed (by omega)).label (cyclicSucc target) =
        Sum.inl after) :
    before = after ∧ i ≠ before := by
  let Z := attachedSelectedPicture_geometric_cutBigCycle
    A hA B D C family selected e R f T U hShared hRel μ
    K owner hAllowed (by omega : 2 ≤ cyclicOwnerChanges owner)
  have hPredSucc : trainCyclicPred target = cyclicSucc target :=
    trainCyclicPred_eq_cyclicSucc_of_card_two hTwo target
  have hEqual : before = after := by
    have hSum : (Sum.inl before : I ⊕ CoreEdge) = Sum.inl after := by
      calc
        Sum.inl before = Z.label (trainCyclicPred target) := hBefore.symm
        _ = Z.label (cyclicSucc target) := by rw [hPredSucc]
        _ = Sum.inl after := hAfter
    exact Sum.inl.inj hSum
  have hDifferentLabels :
      Z.label (trainCyclicPred target) ≠ Z.label target := by
    have hAdj := Z.adjacent_ne (trainCyclicPred target)
    simpa only [cyclicSucc_trainCyclicPred_of_two_le
      (by omega : 2 ≤ cyclicOwnerChanges owner) target] using hAdj
  refine ⟨hEqual, ?_⟩
  intro heq
  apply hDifferentLabels
  calc
    Z.label (trainCyclicPred target) = Sum.inl before := hBefore
    _ = Sum.inl i := by rw [heq]
    _ = Z.label target := hTarget.symm

/-- The two-cut ALL-DESIGNATED alternative in the checked Path A rank
gate is in fact a two-standard alternative: the selected supreme
standard and the other standard are distinct, and the other standard
is the exact label at BOTH neighboring reduced positions. -/
theorem attachedSelectedPicture_two_cut_actual_two_standard_residual
    {n : ℕ} (K : (Out).BigCycle n)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ j, GeomAllowed (K.label j) (owner j))
    (hTwo : cyclicOwnerChanges owner = 2)
    (hResidual : ∃ (target : Fin (cyclicOwnerChanges owner)),
      ∃ i before after : I,
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).HasSupremeAt Wit target ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label target = Sum.inl i ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label (trainCyclicPred target) =
            Sum.inl before ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label (cyclicSucc target) =
            Sum.inl after) :
    ∃ (target : Fin (cyclicOwnerChanges owner)),
      ∃ i j : I, i ≠ j ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).HasSupremeAt Wit target ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label target = Sum.inl i ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label (trainCyclicPred target) =
            Sum.inl j ∧
        (attachedSelectedPicture_geometric_cutBigCycle
          A hA B D C family selected e R f T U hShared hRel μ
          K owner hAllowed (by omega)).label (cyclicSucc target) =
            Sum.inl j := by
  obtain ⟨target, i, before, after, hSupreme, hTarget, hBefore, hAfter⟩ :=
    hResidual
  obtain ⟨hEqual, hDifferent⟩ :=
    attachedSelectedPicture_two_cut_designated_neighbors_eq_distinct
      A hA B D C family selected e R f T U hShared hRel μ
      K owner hAllowed hTwo target i before after
      hTarget hBefore hAfter
  exact ⟨target, i, before, hDifferent, hSupreme,
    hTarget, hBefore, by simpa only [hEqual] using hAfter⟩

end ActualTwoCutStandards
end StructuralRamsey.Girth
