import Girth.TrainFillingShorterArrowPhysicalOldWords
import Girth.TrainFillingClosedTargetMonochromaticEdges
import Girth.TrainFillingIndexedSelectedColourWord

set_option Elab.async false

/-!
# A single genuinely selected shorter M-copy and EHN W* colour arrow

The two colour selection steps share one ambient complete local edge
palette, but have different jobs. The shorter DESIGNATED arrow chooses
an actual selected M copy b (not an arbitrary relational copy) and an
injective old-edge map beta whose whole colour word is constant.
The EHN closed-target arrow chooses one strong W* component c whose
actual selected local support carriers all have a common colour in
that same word. The checked heterogeneous physical-edge equivalence
then supplies a monochromatic image of ALL target physical edges.

We explicitly identify the indexed choice family with the genuine
EHN family; we do not postulate an abstract hLocalArrow or hOldArrow.
The conclusion retains b in S.selected and equality of every beta
carrier with its genuine selected M-image. The old source train is
still supplied as S.targetTrain: identifying this with the genuine
contracted train and assembling the T-labelled target geometry are
separate nontrivial obligations. No final forest theorem is claimed.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA WB V P X Base : Type v} {κ : Type w}

/-- Compose the actual EHN-selected local target with the actual
shorter DESIGNATED M-arrow, while preserving the selected b and its
complete physical old-edge map. Both colour arrows are genuine; the
remaining hypotheses express the relational M-support and the
ambient H's exact physical template/old-edge families. -/
theorem ehnIndexedTarget_monochromatic_of_designatedArrow
    (A : RelStructure L UA) (B : RelStructure L WB)
    [Nonempty WB] [Nontrivial X]
    (K : StructuralRamsey.Structure (closureLanguage L) X)
    (hEhn : ClosedTargetRamseyFamily A B K κ)
    (hStrong : ∀ b : StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K,
      AStrong A (closureRelReduct K)
        (copyCarrier (targetEmbeddingRel b)))
    (hCovered : ∀ x : WB, ∃ a : Embedding A B, x ∈ copyCarrier a)
    (oldCarrier : P → Set V)
    (identify : ∀ p : P, {x : V // x ∈ oldCarrier p} ≃ WB)
    (U : (StructuralRamsey.Structure.Embedding
        (targetClosureExpansion A B) K) → PrivateWagonInput V P X)
    (hU : U = ehnIndexedPrivateChoiceFamily A B K
      hStrong hCovered oldCarrier identify)
    [Nonempty ((StructuralRamsey.Structure.Embedding
      (targetClosureExpansion A B) K) × P)]
    (M : RelStructure L (IndexedPrivateChoice.Vertex U))
    (D : RelStructure L Base)
    (family : Set (Embedding M D))
    {t : List ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A M) t.length)
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t T allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (hTemplateEdges :
      H.templateEdges = supportCopies A (closureRelReduct K))
    (hSupport : supportCopies A M =
      Set.range (IndexedPrivateChoice.contractedCarrier U))
    (hLinear :
      ∀ c : StructuralRamsey.Structure.Embedding
          (targetClosureExpansion A B) K,
        ∀ p q : P, p ≠ q →
        ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    (hArrow : TrainRecursiveWitness.DesignatedArrow S
      (H.TemplateEdge → κ))
    (χ : H.toTrainFilling.NewEdge → κ) :
    ∃ hTemplate : ∀ c, (U c).templateEdges = H.templateEdges,
      ∃ b : DesignatedCopy M D S.system family,
        b ∈ S.selected ∧
        ∃ β : ((StructuralRamsey.Structure.Embedding
            (targetClosureExpansion A B) K) × P) ↪ H.OldEdge,
          (∀ cp, (β cp).1 =
            b.embedding.toFunctionEmbedding ''
              IndexedPrivateChoice.contractedCarrier U cp) ∧
          ∃ c : StructuralRamsey.Structure.Embedding
              (targetClosureExpansion A B) K,
            ∃ colour : κ,
              ∀ a : IndexedPrivateChoice.Edge U,
                a ∈ IndexedPrivateChoice.targetEdges U c →
                  χ (IndexedPrivateChoice.selectedIndexedFilledEdgeEmbedding
                    U H hTemplate β a) = colour := by
  classical
  subst U
  let U := ehnIndexedPrivateChoiceFamily A B K
    hStrong hCovered oldCarrier identify
  have hTemplateR : ∀ c, (U c).templateEdges =
      supportCopies A (closureRelReduct K) := by
    intro c
    exact ehnIndexedPrivateChoiceFamily_templateEdges A B K
      hStrong hCovered oldCarrier identify c
  have hTemplate : ∀ c, (U c).templateEdges = H.templateEdges := by
    intro c
    exact (hTemplateR c).trans hTemplateEdges.symm
  obtain ⟨b, hb, β, ρ, hWords, hCarriers⟩ :=
    IndexedPrivateChoice.contractedOldEdge_commonWord_of_designatedArrow
      U A M D family T allowed S H hOld hSupport hLinear hArrow
      (H.colourWord χ)
  let ρR : {E : Set X // E ∈ supportCopies A (closureRelReduct K)} → κ :=
    fun e => ρ ⟨e.1, by rw [hTemplateEdges]; exact e.2⟩
  obtain ⟨c, colour, hLocalR⟩ :=
    closedTargetRamseyFamily_indexedSelectedEdges_monochromatic
      A B K hEhn hStrong hCovered oldCarrier identify ρR
  have hLocal :
      ∀ p : P, ∀ e : H.TemplateEdge,
        e ∈ IndexedPrivateChoice.selectedCommonEdges U
          H.templateEdges hTemplate c p → ρ e = colour := by
    intro p e he
    obtain ⟨e₀, he₀, heq⟩ := he
    let eR := IndexedPrivateChoice.choiceTemplateEquiv U
      (supportCopies A (closureRelReduct K)) hTemplateR c e₀
    have hSelectedR :
        eR ∈ IndexedPrivateChoice.selectedCommonEdges U
          (supportCopies A (closureRelReduct K)) hTemplateR c p :=
      ⟨e₀, he₀, rfl⟩
    have hColourR : ρR eR = colour := hLocalR p eR hSelectedR
    calc
      ρ e = ρ (IndexedPrivateChoice.choiceTemplateEquiv U
          H.templateEdges hTemplate c e₀) := congrArg ρ heq.symm
      _ = ρR eR := rfl
      _ = colour := hColourR
  refine ⟨hTemplate, b, hb, β, hCarriers, c, colour, ?_⟩
  exact IndexedPrivateChoice.selectedIndexedTargetEdges_colourWord_constant
    U H hTemplate β χ ρ c colour
    (fun p => hWords (c, p)) hLocal

end StructuralRamsey.Girth
