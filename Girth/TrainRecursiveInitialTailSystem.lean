import Girth.TrainRecursiveInitialTailIncidence
import Girth.TrainRecursiveInitialTailBudget
import Girth.TrainEdgeOnlyConstantParent
import Girth.InitialForestCompletion

/-!
# Actual initial system girth from natural target cut bounds

At every proper initial cut, all cycles stay in one literal target component.
A designated occurrence is therefore supreme with the existing identity
replacement plan.  An edge-only acceptable cycle is impossible: source order
bounds its used parent labels; labelled cut girth then makes its parent word
constant; A1--A3 and physical edge linearity rule out that constant case.

The final theorem assumes target physical A-linearity and target labelled
horizontal-cut girth at the requested cutoff.  It derives the complete
initial system-girth statement, including both physical linearity and genuine
globally simultaneous supremeness.  No initial output bound is assumed.
-/

namespace StructuralRamsey.Girth

universe u v

namespace OrderOneData.BigCycle

variable {V E I P : Type v} {D : OrderOneData V E I P}

/-- Target labelled cut girth excludes every acceptable edge-only source
cycle of order at most `q`.  The used-label bound is proved from the actual
source order before applying the finite incidence contradiction. -/
theorem false_of_edge_only_of_labelledCutGirth
    {n : ℕ} (C : D.BigCycle n)
    (edge : Fin n → E) (hLabel : ∀ i, C.label i = Sum.inr (edge i))
    (hEdgeLinear : ∀ e f : E, e ≠ f →
      (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hAccept : C.Acceptable)
    (q : ℕ) (hq : 2 ≤ q)
    (hCut : LabelledGirthGT (fun p => {x | D.WagonVertex p x}) q)
    (hOrder : C.twiceOrder ≤ 2 * q) : False := by
  have hConstant : ∀ i j : Fin n, D.parent (edge i) = D.parent (edge j) := by
    by_contra hNonconstant
    push Not at hNonconstant
    have hCard := C.used_parent_card_le_of_twiceOrder_le edge hLabel
      hNonconstant q hOrder
    have hAll := C.parent_constant_of_labelledCutGirth_of_used_card
      edge hLabel q hq hCut hCard
    obtain ⟨i, j, hij⟩ := hNonconstant
    exact hij (hAll i j)
  let zero : Fin n := ⟨0, by have := C.length_ge_two; omega⟩
  exact C.false_of_edge_only_constant_parent edge hLabel (D.parent (edge zero))
    (fun i => hConstant i zero) hEdgeLinear hAccept

end OrderOneData.BigCycle

namespace TrainRecursiveWitness

variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The actual initial picture satisfies full circulation system girth at
a proper cut from that target's natural labelled cut bound and physical
A-linearity.  The head support-girth hypothesis may supply A-linearity;
larger tail bounds are supplied at their own target horizontal cuts.
-/
theorem initialTrain_fullSystemGirth_of_targetCut
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Nonempty VB]
    (D : RelStructure L P)
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m) (hm : 0 < m)
    (μ : Fin (m + 1)) (hμ : μ.val < m) (q : ℕ) (hq : 2 ≤ q)
    (hTargetLinear : ALinear A B)
    (hTargetCut : LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.1) μ) q) :
    (selectedPictureOrderOneData A B D
      (StructuralRamsey.Partite.Initial.picture B
        (fun b : family => b.1.toFunctionEmbedding))
      family (initialSelected B D family)
      (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding) T hm) μ).FullSystemGirthGT q := by
  classical
  let β : family → VB ↪ P := fun b => b.1.toFunctionEmbedding
  let C₀ := StructuralRamsey.Partite.Initial.picture B β
  let T₀ := initialTrain A hA B β T hm
  let O := selectedPictureOrderOneData A B D C₀ family
    (initialSelected B D family) T₀ μ
  have hCut : LabelledGirthGT (T₀.wagonClassCarrier (fun edge => edge.1) μ) q :=
    initialTrain_labelledCutGirth A hA B β T hm μ hμ q hTargetCut
  have hLinear : O.LinearPretrain :=
    selectedPicture_linearPretrain_of_labelledCutGirth A B D C₀ family
      (initialSelected B D family) T₀ μ
      (initialPicture_aLinear A hA B β hTargetLinear) hq hCut
  have hWagonCarrier :
      (fun p => {x | O.WagonVertex p x}) =
        T₀.wagonClassCarrier (fun edge => edge.1) μ := by
    funext p
    ext x
    exact selectedPicture_wagonVertex_iff A B D C₀ family
      (initialSelected B D family) T₀ μ p x
  have hIncidenceCut : LabelledGirthGT (fun p => {x | O.WagonVertex p x}) q := by
    rw [hWagonCarrier]
    exact hCut
  change O.FullSystemGirthGT q
  refine ⟨hLinear, ?_⟩
  intro n C hAccept hOrder
  by_cases hDesignated : ∃ k : Fin n, O.designated (C.label k)
  · exact initialCycle_hasSupreme_of_designated A hA B D family T hm μ hμ C hDesignated
  · have hEdge : ∀ k : Fin n, ∃ edge, C.label k = Sum.inr edge := by
      intro k
      cases hLabel : C.label k with
      | inr edge => exact ⟨edge, rfl⟩
      | inl copy =>
          exact (hDesignated ⟨k, by simp only [hLabel, OrderOneData.designated]⟩).elim
    choose edge hLabel using hEdge
    exact (C.false_of_edge_only_of_labelledCutGirth edge hLabel hLinear.1
      hAccept q hq hIncidenceCut hOrder).elim

end TrainRecursiveWitness
end StructuralRamsey.Girth
