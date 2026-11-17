import Girth.FiniteTracePictureExtraction
import Girth.SupportedTreeOrderReduct

/-! # Small induced structures after forgetting the order -/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P X : Type v}

/-- Apply the exact outer-picture endpoint and then restrict to the
unordered language. For the uniform edge language, this is the
induced-subhypergraph conclusion for the order reduct of the witness. -/
theorem smallInducedStructure_orderReduct_of_assembledPicture
    (A : RelStructure L.withOrder UA) (B : RelStructure L.withOrder VB)
    (D : RelStructure L.withOrder P) (C : StructuralRamsey.Partite.System L.withOrder P X)
    [Finite X]
    (family : Set (Embedding B D))
    (hCover : DesignatedCoversIrreducibles B D C family)
    (hShared : DesignatedSharedSupport A C family)
    (q : ℕ) (hq : 1 ≤ q)
    (hComplete : ForestCompletionProperty
      (testedPictureABSupport A B D C family)
      (designatedPictureASupport A B D C family) q)
    (Z : Set X) (hBudget : Z.ncard ≤ q)
    (alphaB : Embedding A B) (a₀ a₁ : UA) (hne : a₀ ≠ a₁) :
    ∃ (Y : Type v) (T : RelStructure L Y)
        (_ : Embedding (C.toRelStructure.orderReduct.induce Z) T),
      ASupportedTreeAmalgam A.orderReduct B.orderReduct Y T :=
  smallInducedStructure_orderReduct
    (smallInducedStructure_embeds_supportedTree_of_assembledPicture
      A B D C family hCover hShared q hq hComplete Z hBudget alphaB a₀ a₁ hne)

end StructuralRamsey.Girth
