import Girth.TrainActualZeroCutBigCycle
import Girth.TrainActualStandardRestrictionMap

/-!
# One-standard / zero-cut physical cycle: full acceptability pullback

The previous modules construct a genuinely legal OLD BigCycle with
exact selected labels and genuine standard vertex/wagon connector
images. The actual standard restriction geometry supplies its
conditional cyclic RestrictionMap, automatically discharging all
old-to-output wagon contacts and ambient pair edges.

The exact connector-kind word is unchanged, so the two numeric
orders are EQUAL, not merely bounded. If the output cycle is
acceptable, A1 of the old word follows from literal preservation of
designated labels, even when physical carriers coincide; A2/A3
follow from the verified cyclic restriction theorem.

This settles the local one-standard ACCEPTABILITY transfer (given
the explicit nontrivial A-strong designated target hypotheses).
Lifting globally legal simultaneous supreme plans and the full
system-Girth induction remain separate. No appendix.
-/

namespace StructuralRamsey.Girth

namespace OrderOneData

universe v w
variable {V E I P : Type v} {V' E' I' P' : Type w}
variable {D : OrderOneData V E I P} {D' : OrderOneData V' E' I' P'}

/-- A cyclic word with an EXACT connector image has exactly the same
numerical twice-order. This is independent of any wagon/copy labels. -/
theorem BigCycle.twiceOrder_eq_of_connectorImage
    {n : ℕ} (K : D.BigCycle n) (Z : D'.BigCycle n)
    (vertex : V' → V) (wagon : P' → P)
    (hConnector : ∀ k : Fin n,
      K.connector k = Sum.map vertex wagon (Z.connector k)) :
    K.twiceOrder = Z.twiceOrder := by
  have hKind (k : Fin n) :
      connectorKind (K.connector k) =
        connectorKind (Z.connector k) := by
    rw [hConnector k]
    cases Z.connector k <;> rfl
  simp only [BigCycle.twiceOrder]
  apply Finset.sum_congr rfl
  intro k _
  rw [hKind k, hKind (cyclicSucc k)]

end OrderOneData

open StructuralRamsey.RelStructure
universe u v
section ZeroCutAcceptability

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
local notation "OldEdge" => OldACarrierEdge A C.toRelStructure
local notation "CoreEdge" => OldACarrierEdge A R
local notation "Selected" => {q : DesignatedCopy B D C family // q ∈ selected}
local notation "Std" =>
  RelStructure.Attachment.copyEmbedding C.toRelStructure S R f
local notation "StdWagon" => generatedActualASupportTrain_standardWagonEmbedding
  A hA C.toRelStructure S R f T U hRel hShared μ
local notation "LabelMap" => attachedSelectedPictureLabel
  A hA B D C family selected e R f
local notation "Old" => selectedPictureOrderOneData
  A B D C family selected T μ
local notation "Out" => attachedSelectedPictureOrderOneData
  A hA B D C family selected e R f T U hShared μ
local notation "GeomAllowed" => selectedOutputGeometricOwnerAllowed
  A hA B D C family selected e R f T U hShared μ

include hRel

/-- An acceptable output cycle with ZERO geometrical cuts has a
genuinely acceptable old selected-picture BigCycle in ONE standard,
with literal designated labels, literal physical connector images
and IDENTICAL numerical twice-order. A1 follows from label identity,
and A2/A3 from the actual standard RestrictionMap. -/
theorem attachedSelectedPicture_zero_cut_acceptable_oldBigCycle [Finite UA]
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hTwo : ∀ q : Selected, ∃ r s : OldEdge,
      r ≠ s ∧ r.1 ⊆ copyCarrier q.1.embedding ∧
        s.1 ⊆ copyCarrier q.1.embedding)
    {n : ℕ} (K : (Out).BigCycle n)
    (hAccept : K.Acceptable)
    (owner : Fin n → I ⊕ CoreEdge)
    (hAllowed : ∀ k : Fin n, GeomAllowed (K.label k) (owner k))
    (hZero : cyclicOwnerChanges owner = 0) :
    ∃ (i : I) (Z : (Old).BigCycle n),
      (∀ k : Fin n, LabelMap i (Z.label k) = K.label k) ∧
      (∀ k : Fin n,
        Sum.map (Std i) (StdWagon i) (Z.connector k) =
          K.connector k) ∧
      Z.Acceptable ∧ Z.twiceOrder = K.twiceOrder := by
  obtain ⟨i, Z, hLabels, hConnectors⟩ :=
    attachedSelectedPicture_zero_cut_oldBigCycle
      A hA B D C family selected e R f T U hShared hRel μ
      hStrong hTwo K owner hAllowed hZero
  have hMap : K.RestrictionMap Z :=
    attachedSelectedPicture_standard_restrictionMap
      A hA B D C family selected e R f T U hShared hRel μ
      i K Z (fun k => (hConnectors k).symm)
  have hOrder : K.twiceOrder = Z.twiceOrder :=
    OrderOneData.BigCycle.twiceOrder_eq_of_connectorImage
      K Z (Std i) (StdWagon i)
      (fun k => (hConnectors k).symm)
  have hDesignated :
      Z.twiceOrder = 2 →
        ∃ k : Fin n, (Old).designated (Z.label k) := by
    intro hZOne
    obtain ⟨k, hk⟩ := hAccept.1 (hOrder.trans hZOne)
    refine ⟨k, ?_⟩
    cases hLabel : Z.label k with
    | inl q =>
        trivial
    | inr old =>
        have hOutLabel :
            K.label k = LabelMap i (Sum.inr old) := by
          calc
            K.label k = LabelMap i (Z.label k) := (hLabels k).symm
            _ = LabelMap i (Sum.inr old) := by rw [hLabel]
        have hContradiction : ¬ (Out).designated (K.label k) := by
          rw [hOutLabel]
          simp [OrderOneData.designated, attachedSelectedPictureLabel]
        exact False.elim (hContradiction hk)
  have hOldAccept : Z.Acceptable :=
    hMap.acceptable hAccept hDesignated
  exact ⟨i, Z, hLabels, hConnectors, hOldAccept, hOrder.symm⟩

end ZeroCutAcceptability
end StructuralRamsey.Girth
