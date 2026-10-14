import Girth.TrainActualWagonThreeLink
import Girth.TrainWagonClassRestriction

/-!
# Circulation: the edge-block two-standard argument with shared witnesses

A physical edge block `e₁ W e₂` containing boundary vertices
y in e₁ and x in e₂ determines its old wagon through x,y.
Two genuine shared edges in one old wagon, one through x and one
through y, consequently lie in the SAME wagon as this block:
otherwise old wagon linearity would fail.

This combines with the checked actual A-support three-link quotient:
if the two standard blocks admit such shared witness pairs, and their
first core images lie in the same core wagon, the two block wagons
become equivalent in the generated actual relational attachment.

The shared witness-pair existence/physical incidence is EXPLICIT,
not silently inferred from the fact that a designated copy meets a
wagon. The complete edge-only two-standard lemma still needs this
existence derived from the local two-copy long witnesses and the
shared-subtrain embeddings. No appendix is used.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {E V : Type v}

/-- Old linearity gives the elementary `edge block -> shared witness
edge` wagon relation: two different vertices belong both to the
block wagon (a,b) and the shared-pair wagon (c,d), so these wagon
labels cannot be different. No equality of physical edge labels or
carriers is assumed. -/
theorem EdgeTrainLevels.rel_of_crossing_edge_pairs
    {m : ℕ} (T : EdgeTrainLevels E m)
    (carrier : E → Set V) (μ : Fin (m + 1))
    (hLinear : ∀ p q : Quotient (T.wagonSetoid μ),
      p ≠ q →
      (T.wagonClassCarrier carrier μ p ∩
        T.wagonClassCarrier carrier μ q).Subsingleton)
    (a b c d : E) (x y : V) (hxy : x ≠ y)
    (hab : T.rel μ a b) (hcd : T.rel μ c d)
    (hay : y ∈ carrier a) (hbx : x ∈ carrier b)
    (hcx : x ∈ carrier c) (hdy : y ∈ carrier d) :
    T.rel μ a c := by
  let p : Quotient (T.wagonSetoid μ) :=
    Quotient.mk (T.wagonSetoid μ) a
  let q : Quotient (T.wagonSetoid μ) :=
    Quotient.mk (T.wagonSetoid μ) c
  have hxP : x ∈ T.wagonClassCarrier carrier μ p := by
    change x ∈ T.wagonCarrier carrier μ a
    exact ⟨b, hab, hbx⟩
  have hyP : y ∈ T.wagonClassCarrier carrier μ p := by
    change y ∈ T.wagonCarrier carrier μ a
    exact ⟨a, (T.equivalent μ).refl a, hay⟩
  have hxQ : x ∈ T.wagonClassCarrier carrier μ q := by
    change x ∈ T.wagonCarrier carrier μ c
    exact ⟨c, (T.equivalent μ).refl c, hcx⟩
  have hyQ : y ∈ T.wagonClassCarrier carrier μ q := by
    change y ∈ T.wagonCarrier carrier μ c
    exact ⟨d, hcd, hdy⟩
  have hpq : p = q := by
    by_contra hneq
    exact hxy ((hLinear p q hneq)
      ⟨hxP, hxQ⟩ ⟨hyP, hyQ⟩)
  exact Quotient.exact hpq

variable {L : RelLanguage.{u}}
variable {UA Old Core I : Type v}

/-- Entire real-output edge-block quotient chain, assuming the
literal shared long-piece witnesses and the old wagon linearity.

The first standard block has y in its left edge and x in its
right edge; the second has x in its left edge and y in its
right edge. The two core long pieces are represented by genuine
shared old edges (sx,sy) and (tx,ty). Reflection on the shared
subtrain moves each core pair into a single old wagon. Then the
old linearity argument supplies the two outer relations needed
by the existing actual three-link transport theorem. -/
theorem generatedActualASupportTrain_edgeBlocks_of_shared_pairs
    {m : ℕ}
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L Old) (S : Set Old)
    (D : RelStructure L Core)
    (f : I → RelStructure.Embedding (B.induce S) D)
    (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
    (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
    (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A B S))
    (μ : Fin (m + 1)) (i j : I)
    (e₁ e₂ e₃ e₄ : OldACarrierEdge A B)
    (sx sy tx ty : SharedOldACarrierEdge A B S)
    (x y : RelStructure.Attachment.Vertex S (W := Core) (I := I))
    (hxy : x ≠ y)
    (hLinear : ∀ k : I,
      ∀ p q : Quotient (oldTrain.wagonSetoid μ), p ≠ q →
        (oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B S D f k) μ p ∩
         oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B S D f k) μ q).Subsingleton)
    (hBlockI : oldTrain.rel μ e₁ e₂)
    (hBlockJ : oldTrain.rel μ e₃ e₄)
    (hSharedReflect : ∀ (k : I)
        (s t : SharedOldACarrierEdge A B S),
      coreTrain.rel μ
        (sharedOldACarrierCoreEmbedding A B S D f k s)
        (sharedOldACarrierCoreEmbedding A B S D f k t) →
      oldTrain.rel μ
        (sharedOldACarrierInclusion A B S s)
        (sharedOldACarrierInclusion A B S t))
    (hLongCoreI : coreTrain.rel μ
      (sharedOldACarrierCoreEmbedding A B S D f i sx)
      (sharedOldACarrierCoreEmbedding A B S D f i sy))
    (hLongCoreJ : coreTrain.rel μ
      (sharedOldACarrierCoreEmbedding A B S D f j tx)
      (sharedOldACarrierCoreEmbedding A B S D f j ty))
    (hCommonCore : coreTrain.rel μ
      (sharedOldACarrierCoreEmbedding A B S D f i sx)
      (sharedOldACarrierCoreEmbedding A B S D f j tx))
    (hY₁ : y ∈ attachedOldAEdgeCarrier A B S D f i e₁)
    (hX₂ : x ∈ attachedOldAEdgeCarrier A B S D f i e₂)
    (hX₃ : x ∈ attachedOldAEdgeCarrier A B S D f j e₃)
    (hY₄ : y ∈ attachedOldAEdgeCarrier A B S D f j e₄)
    (hSX : x ∈ attachedOldAEdgeCarrier A B S D f i
      (sharedOldACarrierInclusion A B S sx))
    (hSY : y ∈ attachedOldAEdgeCarrier A B S D f i
      (sharedOldACarrierInclusion A B S sy))
    (hTX : x ∈ attachedOldAEdgeCarrier A B S D f j
      (sharedOldACarrierInclusion A B S tx))
    (hTY : y ∈ attachedOldAEdgeCarrier A B S D f j
      (sharedOldACarrierInclusion A B S ty)) :
    (generatedActualASupportTrain A hA B S D f
      oldTrain coreTrain hShared).rel μ
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) i e₁))
      (actualAPictureEdgeEquiv A hA B S D f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A B S)
          (sharedOldACarrierCoreEmbedding A B S D f) j e₃)) := by
  let inOld := sharedOldACarrierInclusion A B S
  let inCore := sharedOldACarrierCoreEmbedding A B S D f
  have hOldI : oldTrain.rel μ e₁ (inOld sx) :=
    oldTrain.rel_of_crossing_edge_pairs
      (attachedOldAEdgeCarrier A B S D f i)
      μ (hLinear i) e₁ e₂ (inOld sx) (inOld sy)
      x y hxy hBlockI
      (hSharedReflect i sx sy hLongCoreI)
      hY₁ hX₂ hSX hSY
  have hBlockJRev : oldTrain.rel μ e₄ e₃ :=
    (oldTrain.equivalent μ).symm hBlockJ
  have hOldJFirst : oldTrain.rel μ e₄ (inOld tx) :=
    oldTrain.rel_of_crossing_edge_pairs
      (attachedOldAEdgeCarrier A B S D f j)
      μ (hLinear j) e₄ e₃ (inOld tx) (inOld ty)
      x y hxy hBlockJRev
      (hSharedReflect j tx ty hLongCoreJ)
      hY₄ hX₃ hTX hTY
  have hOldJ : oldTrain.rel μ (inOld tx) e₃ :=
    (oldTrain.equivalent μ).trans
      ((oldTrain.equivalent μ).symm hOldJFirst)
      hBlockJRev
  exact generatedActualASupportTrain_three_link
    A hA B S D f oldTrain coreTrain hShared μ
      i j e₁ e₃ sx tx hOldI hCommonCore hOldJ

end StructuralRamsey.Girth
