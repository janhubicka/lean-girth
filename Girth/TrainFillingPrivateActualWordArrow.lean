import Girth.TrainFillingPrivateActualOrderParent
import Girth.TrainFillingPrivateSelectedOldRange
import Girth.TrainFillingIndexedSelectedColourWord

set_option Elab.async false

/-!
# The actual lower-stage Ramsey arrow gives complete old-edge words

The final indexed filling lemma colours EVERY physical old N edge f
by the entire function e ↦ χ(H.edgeEquiv(f,e)).

The shorter OrderStage Ramsey arrow is expressed on relational
A-embeddings into N, not on physical old-edge carriers. Because the
canonical filling uses the FULL A-support of N and the actual M
support is exactly the contracted first-wagon family, a colouring
of old physical edges pulls back to A-embeddings. The selected
OrderStage B-copy then has the same COMPLETE word on every
contracted first-wagon edge, including all choices simultaneously.

This constructs the hOldArrow used by
selectedIndexedTargetEdges_ramsey_of_two_arrows from an ACTUAL
selected lower-stage Ramsey arrow. It does not assume an arbitrary
old-edge injection, and it retains the genuine selected copy
label b. The source nonempty A-embedding is necessary to choose
the constant common colour-word.

The remaining higher-level tasks are the precise EHN local arrow,
selected target vertex/ordered-train realization and filled girth.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v w

variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- For a genuine selected lower OrderStage, the selected A-copy
arrow on complete local-template colour words yields an injection
of ALL contracted first-wagon edges with a common full word.

The witness β is exactly the physical map of the same selected
relational M-copy b. Neither edge ownership nor monochromaticity
on unselected local words is postulated. -/
theorem actualOrderStage_oldColourWordArrow
    [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.OrderStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (H : UniformFillingData S.Vertex X)
    (hOld : H.oldEdges = supportCopies A S.system.toRelStructure)
    (κ : Type w)
    (hSourceA : Nonempty (Embedding A M))
    (hArrow : TrainRecursiveWitness.DesignatedArrow
      S.toForestTailStage (H.TemplateEdge → κ)) :
    ∀ word : H.OldEdge → H.TemplateEdge → κ,
      ∃ (β : (C × P) ↪ H.OldEdge)
        (ρ : H.TemplateEdge → κ),
        ∀ cp : C × P, word (β cp) = ρ := by
  classical
  intro word
  let χ : Embedding A S.system.toRelStructure → H.TemplateEdge → κ :=
    fun a => word ⟨copyCarrier a, by
      rw [hOld]
      exact ⟨a, rfl⟩⟩
  obtain ⟨b, hb, hMono⟩ := hArrow χ
  let β := actualSelectedFilledOldEdgeEmbedding U A M T hm
    hSupport hLinear D family allowed S.toForestTailStage b H hOld
  let a₀ : Embedding A M := Classical.choice hSourceA
  refine ⟨β, χ (b.embedding.comp a₀), ?_⟩
  intro cp
  let e := contractedPhysicalEdgeEquiv U A M hSupport hLinear cp
  obtain ⟨a, ha⟩ := e.2
  have hCarrier : (β cp).1 = copyCarrier (b.embedding.comp a) := by
    calc
      (β cp).1 =
          b.embedding.toFunctionEmbedding '' contractedCarrier U cp :=
        actualSelectedFilledOldEdgeEmbedding_carrier U A M T hm
          hSupport hLinear D family allowed S.toForestTailStage b H hOld cp
      _ = b.embedding.toFunctionEmbedding '' e.1 := by
        rw [contractedPhysicalEdgeEquiv_carrier]
      _ = b.embedding.toFunctionEmbedding '' copyCarrier a := by rw [ha]
      _ = copyCarrier (b.embedding.comp a) :=
        UniformPrivateTemplate.image_copyCarrier_comp
          A M S.system.toRelStructure b.embedding a
  have hEq :
      β cp = (⟨copyCarrier (b.embedding.comp a), by
        rw [hOld]
        exact ⟨b.embedding.comp a, rfl⟩⟩ : H.OldEdge) := by
    apply Subtype.ext
    exact hCarrier
  calc
    word (β cp) = χ (b.embedding.comp a) := by
      change word (β cp) =
        word (⟨copyCarrier (b.embedding.comp a), by
          rw [hOld]
          exact ⟨b.embedding.comp a, rfl⟩⟩ : H.OldEdge)
      exact congrArg word hEq
    _ = χ (b.embedding.comp a₀) := hMono a a₀

end StructuralRamsey.Girth.IndexedPrivateChoice
