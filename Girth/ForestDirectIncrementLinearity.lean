import Girth.ForestActualRecursiveIncrement
import Girth.ActiveCarrierStrong
import Girth.LinearityGirthTwo
import Girth.ForestTwoMemberLinearity

/-!
# The direct forest increment without a circular output-girth premise

The older actual partite forest-increment endpoint assumes that the
OUTPUT support already has girth greater than two. In the manuscript
this follows independently: old-picture mixed forests through q >= 2, local-core
girth > m >= 2, base A-linearity and rigidity, and A-strong gluing
images imply output A-linearity by the checked attachment geometry.

This wrapper also derives old-picture A-linearity from its genuine
two-member mixed-forest hypothesis; no extra old-linearity input remains.
It supplies output linearity before applying
the existing finite mixed forest theorem, including its m=2 case.
It neither constructs the local Ramsey witness nor assumes the
desired output forest property.

SOURCE CANDIDATE: a local Lean build and axiom audit remain pending.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure
universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Direct q>=2 mixed forest increment from the old and local
geometric hypotheses, with output girth-two derived rather than
postulated. At q=2 the original endpoint's explicit whole-image
strongness and cutoff-two case remain in force. -/
theorem actualPartiteDesignatedAB_mixedForest_of_strongLinearStep
    (A : RelStructure L UA) (hA : A.Irreducible) [Finite UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hPartite : C.IsPartiteOver D)
    (hBaseLinear : ALinear A D)
    (family : Set (RelStructure.Embedding B D))
    (selectedOld : Set (DesignatedCopy B D C family))
    (e : RelStructure.Embedding A D)
    (hRigid : ∀ b : RelStructure.Embedding A D,
      SameCopy b e → b = e)
    (hActive : (activeCarrier A C e.toFunctionEmbedding).Nonempty)
    (E : StructuralRamsey.Partite.System L P Y) [Fintype Y]
    (f : I → StructuralRamsey.Partite.Embedding
      (C.induce (activeCarrier A C e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ q : DesignatedCopy B D C family,
      q ∈ selectedOld → AStrong A D (copyCarrier q.base))
    (hLocalStrong : ∀ i : I,
      AStrong A E.toRelStructure (copyCarrier (f i).toEmbedding))
    (m : ℕ) (hm : 2 ≤ m)
    (hLocal : m = 2 ∨
      ((∃ e₀ e₁ : Set (activeCarrier A C e.toFunctionEmbedding),
          e₀ ∈ supportCopies A
            (C.induce (activeCarrier A C e.toFunctionEmbedding)).toRelStructure ∧
          e₁ ∈ supportCopies A
            (C.induce (activeCarrier A C e.toFunctionEmbedding)).toRelStructure ∧
          e₀ ≠ e₁) ∧
        Function.Injective (fun i => bSupportPiece A (f i).toEmbedding) ∧
        FiniteMixedForestThrough
          (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) (m - 1)))
    (hCoreGirth : GirthGT (supportCopies A E.toRelStructure) m)
    (testedOld : HypergraphPiece X → Prop)
    (hOldForest : FiniteMixedForestThrough testedOld m)
    (hTestA : ∀ aOld : RelStructure.Embedding A C.toRelStructure,
      testedOld (HypergraphPiece.oneEdge (copyCarrier aOld)))
    (hTestB : ∀ q : DesignatedCopy B D C family,
      q ∈ selectedOld → testedOld (bSupportPiece A q.embedding)) :
    FiniteMixedForestThrough
      (fun T : HypergraphPiece
        (StructuralRamsey.Partite.Attachment.Vertex
          (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I)) =>
        (∃ aNew : RelStructure.Embedding A
          (StructuralRamsey.Partite.Attachment.attach C
            (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure,
          T = HypergraphPiece.oneEdge (copyCarrier aNew)) ∨
        (∃ i : I, ∃ q : DesignatedCopy B D C family,
          q ∈ selectedOld ∧
          T = bSupportPiece A (q.transportToStandard f i).embedding)) m := by
  have hOldLinear : ALinear A C.toRelStructure :=
    aLinear_of_finiteMixedForestThrough_oneEdges
      A C.toRelStructure testedOld m hm hOldForest hTestA
  have hCoreLinear : ALinear A E.toRelStructure := by
    intro a b hDifferent
    exact pairwise_subsingleton_of_girthGT_two
      (girthGT_mono hCoreGirth hm)
      (show copyCarrier a ∈ supportCopies A E.toRelStructure from ⟨a, rfl⟩)
      (show copyCarrier b ∈ supportCopies A E.toRelStructure from ⟨b, rfl⟩)
      hDifferent
  have hOutputLinear :
      ALinear A
        (StructuralRamsey.Partite.Attachment.attach C
          (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure :=
    (activeAttachment_geometry_of_base_aLinear
      A D C hA hPartite hBaseLinear e hRigid E f
      hOldLinear hCoreLinear hLocalStrong).1
  have hOutputGirthTwo :
      GirthGT
        (supportCopies A
          (StructuralRamsey.Partite.Attachment.attach C
            (activeCarrier A C e.toFunctionEmbedding) E f).toRelStructure) 2 :=
    girthGT_two_of_aLinear A _ hOutputLinear
  exact actualPartiteDesignatedAB_mixedForest_of_relationalLocal
    A hA B D C hPartite hBaseLinear
    family selectedOld e hActive E f hBaseStrong hLocalStrong
    m hm hLocal hCoreGirth hOutputGirthTwo
    testedOld hOldForest hTestA hTestB

end StructuralRamsey.Girth
