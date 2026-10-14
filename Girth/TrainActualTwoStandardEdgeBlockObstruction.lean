import Girth.TrainActualTwoStandardEdgeBlock
import Girth.TrainTwoCopyCommonWagon
import Girth.TrainActualTopParentQuotientBridge

/-!
# Circulation: actual edge-block two-standard obstruction

A copy of the shared subsystem is represented by genuine shared OLD
A-support edges in each standard picture; its corresponding witness
edges are their core images. The earlier local two-copy symmetry plus
linearity says that, unless an ambient witness edge connects x,y,
both local copies have long pieces with edges in the SAME witness
wagon. Membership in a copy's `copyEdges` is literally membership
in the range of the genuine shared-to-core edge embedding. We can
therefore lift all four long-piece edges back to shared OLD edge
labels, with their physical incidences intact.

In a linear OLD standard train, each two-edge block with endpoint
vertices x,y belongs to the same old wagon as that shared pair.
The verified actual old-core-old three-link theorem then identifies
the two output block wagon classes. Consequently two DISTINCT
output wagons force a genuine ambient witness edge through x,y.

The theorem deals with physical EDGE labels of the two blocks.
Arbitrary designated-copy labels in the general two-standard lemma,
cycle reduct legality, global cycle transfer and appendix remain
separate.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {W CoreEdge Shared I : Type v}

/-- Two actual shared-witness copies through x,y have four genuine
shared edge representatives in one core wagon, unless the core
ambient hypergraph contains an edge through x,y.

This strips only the range-extraction and quotient-equality steps
from the already checked two-copy common-long-wagon theorem. -/
theorem sharedWitness_twoCopy_common_shared_pairs
    {m : ℕ}
    (T : EdgeTrainLevels CoreEdge m)
    (μ : Fin (m + 1))
    (embed : I → Shared ↪ CoreEdge)
    (carrier : CoreEdge → Set W)
    (hLinear : (sharedWitnessOrderOneData T μ embed carrier).LinearPretrain)
    (hBound : (sharedWitnessOrderOneData T μ embed carrier).LocalPieceSystemBound 2)
    (i j : I) (x y : W)
    (hij : i ≠ j) (hxy : x ≠ y)
    (hix : x ∈ (sharedWitnessOrderOneData T μ embed carrier).copyCarrier i)
    (hiy : y ∈ (sharedWitnessOrderOneData T μ embed carrier).copyCarrier i)
    (hjx : x ∈ (sharedWitnessOrderOneData T μ embed carrier).copyCarrier j)
    (hjy : y ∈ (sharedWitnessOrderOneData T μ embed carrier).copyCarrier j)
    (hNoEdge : ¬ (sharedWitnessOrderOneData T μ embed carrier).PairEdge x y) :
    ∃ sx sy tx ty : Shared,
      T.rel μ (embed i sx) (embed i sy) ∧
      T.rel μ (embed j tx) (embed j ty) ∧
      T.rel μ (embed i sx) (embed j tx) ∧
      x ∈ carrier (embed i sx) ∧
      y ∈ carrier (embed i sy) ∧
      x ∈ carrier (embed j tx) ∧
      y ∈ carrier (embed j ty) := by
  let C := sharedWitnessOrderOneData T μ embed carrier
  obtain ⟨w, ⟨a, b, ha, hb, hab, haw, hbw, hxa, hyb⟩,
      ⟨c, d, hc, hd, hcd, hcw, hdw, hxc, hyd⟩⟩ :=
    C.twoVertexTwoCopyCycle_common_long_wagon
      hLinear hBound i j x y hij hxy hix hiy hjx hjy hNoEdge
  change a ∈ Set.range (embed i) at ha
  change b ∈ Set.range (embed i) at hb
  change c ∈ Set.range (embed j) at hc
  change d ∈ Set.range (embed j) at hd
  obtain ⟨sx, hsx⟩ := ha
  obtain ⟨sy, hsy⟩ := hb
  obtain ⟨tx, htx⟩ := hc
  obtain ⟨ty, hty⟩ := hd
  have hFirst : T.rel μ (embed i sx) (embed i sy) := by
    apply Quotient.exact
    rw [hsx, hsy]
    exact haw.trans hbw.symm
  have hSecond : T.rel μ (embed j tx) (embed j ty) := by
    apply Quotient.exact
    rw [htx, hty]
    exact hcw.trans hdw.symm
  have hCross : T.rel μ (embed i sx) (embed j tx) := by
    apply Quotient.exact
    rw [hsx, htx]
    exact haw.trans hcw.symm
  refine ⟨sx, sy, tx, ty, hFirst, hSecond, hCross, ?_, ?_, ?_, ?_⟩
  · rw [hsx]
    exact hxa
  · rw [hsy]
    exact hyb
  · rw [htx]
    exact hxc
  · rw [hty]
    exact hyd

universe u
variable {L : RelLanguage.{u}}
variable {UA Old Core : Type v}

/-- Actual edge-block form of the two-standard obstruction.
The old boundary blocks are two distinct output wagons. If the
witness has no edge through their distinct boundary vertices,
two local long pieces lift to genuine shared old A-support edges.
Old wagon linearity and the verified three-link generator chain
then force the two output wagon labels to coincide, contradicting
their distinctness.

The local witness-copy incidence and physical edge blocks are
explicit hypotheses, not consequences of an illicit global
output-wagon linearity assumption. -/
theorem actualTwoStandard_edgeBlocks_force_core_pairEdge
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
    (x y : RelStructure.Attachment.Vertex S (W := Core) (I := I))
    (hij : i ≠ j) (hxy : x ≠ y)
    (hLinearOld : ∀ k : I,
      ∀ p q : Quotient (oldTrain.wagonSetoid μ), p ≠ q →
        (oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B S D f k) μ p ∩
         oldTrain.wagonClassCarrier
          (attachedOldAEdgeCarrier A B S D f k) μ q).Subsingleton)
    (hBlockI : oldTrain.rel μ e₁ e₂)
    (hBlockJ : oldTrain.rel μ e₃ e₄)
    (hRel : ∀ (k : I) (s t : SharedOldACarrierEdge A B S),
      oldTrain.rel μ
        (sharedOldACarrierInclusion A B S s)
        (sharedOldACarrierInclusion A B S t) ↔
      coreTrain.rel μ
        (sharedOldACarrierCoreEmbedding A B S D f k s)
        (sharedOldACarrierCoreEmbedding A B S D f k t))
    (hY₁ : y ∈ attachedOldAEdgeCarrier A B S D f i e₁)
    (hX₂ : x ∈ attachedOldAEdgeCarrier A B S D f i e₂)
    (hX₃ : x ∈ attachedOldAEdgeCarrier A B S D f j e₃)
    (hY₄ : y ∈ attachedOldAEdgeCarrier A B S D f j e₄)
    (hCoreLinear :
      (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).LinearPretrain)
    (hCoreBound :
      (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).LocalPieceSystemBound 2)
    (hIx : x ∈ (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).copyCarrier i)
    (hIy : y ∈ (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).copyCarrier i)
    (hJx : x ∈ (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).copyCarrier j)
    (hJy : y ∈ (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).copyCarrier j)
    (hDistinctWagons : ¬
      (generatedActualASupportTrain A hA B S D f
        oldTrain coreTrain hShared).rel μ
        (actualAPictureEdgeEquiv A hA B S D f
          (physicalStandardEdge
            (sharedOldACarrierInclusion A B S)
            (sharedOldACarrierCoreEmbedding A B S D f) i e₁))
        (actualAPictureEdgeEquiv A hA B S D f
          (physicalStandardEdge
            (sharedOldACarrierInclusion A B S)
            (sharedOldACarrierCoreEmbedding A B S D f) j e₃))) :
    (sharedWitnessOrderOneData coreTrain μ
        (sharedOldACarrierCoreEmbedding A B S D f)
        (attachedCoreAEdgeCarrier A B S D f)).PairEdge x y := by
  let emb := sharedOldACarrierCoreEmbedding A B S D f
  let car := attachedCoreAEdgeCarrier A B S D f
  let C := sharedWitnessOrderOneData coreTrain μ emb car
  by_contra hNoEdge
  obtain ⟨sx, sy, tx, ty, hLongI, hLongJ, hCore,
      hxsi, hysi, hxtj, hytj⟩ :=
    sharedWitness_twoCopy_common_shared_pairs
      coreTrain μ emb car hCoreLinear hCoreBound
      i j x y hij hxy hIx hIy hJx hJy hNoEdge
  have hSX : x ∈ attachedOldAEdgeCarrier A B S D f i
      (sharedOldACarrierInclusion A B S sx) := by
    rw [attachedSharedAEdgeCarrier_eq A B S D f i sx]
    exact hxsi
  have hSY : y ∈ attachedOldAEdgeCarrier A B S D f i
      (sharedOldACarrierInclusion A B S sy) := by
    rw [attachedSharedAEdgeCarrier_eq A B S D f i sy]
    exact hysi
  have hTX : x ∈ attachedOldAEdgeCarrier A B S D f j
      (sharedOldACarrierInclusion A B S tx) := by
    rw [attachedSharedAEdgeCarrier_eq A B S D f j tx]
    exact hxtj
  have hTY : y ∈ attachedOldAEdgeCarrier A B S D f j
      (sharedOldACarrierInclusion A B S ty) := by
    rw [attachedSharedAEdgeCarrier_eq A B S D f j ty]
    exact hytj
  have hRelOut :=
    generatedActualASupportTrain_edgeBlocks_of_shared_pairs
      A hA B S D f oldTrain coreTrain hShared μ i j
      e₁ e₂ e₃ e₄ sx sy tx ty x y hxy
      hLinearOld hBlockI hBlockJ
      (fun k s t h => (hRel k s t).mpr h)
      hLongI hLongJ hCore
      hY₁ hX₂ hX₃ hY₄ hSX hSY hTX hTY
  exact hDistinctWagons hRelOut

end StructuralRamsey.Girth
