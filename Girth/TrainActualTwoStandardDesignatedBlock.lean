import Girth.TrainStandardPictureFourWagonBoundary
import Girth.TrainActualTwoStandardEdgeBlockObstruction

/-!
# Circulation: pull back arbitrary designated blocks along the real attachment

The block labels below are genuine old designated copies or physical A-edges.
Their endpoint incidences are given in the OUTPUT, as images under the standard
embedding. A long piece consists of genuinely shared old edge representatives.
Injectivity pulls the same physical endpoints back into the old block labels.
If the block wagon differed from the long-piece wagon, this constructs the
literal four-occurrence frame and the checked old bound forces a core pair edge.

Consequently, in the absence of a core pair edge, each block wagon equals its
long-piece wagon. Applying this on both sides and using the checked actual
old-core-old three-link theorem contradicts distinct OUTPUT wagon classes.
No inference from merely meeting a wagon and containing a vertex is made.

The source system bound, witness bound, witness-copy memberships and reflection
of the shared train are explicit hypotheses. Instantiating these uniformly from
the full picture-step record, and general cycle transfer, are separate tasks.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X Y I : Type v}

/-- Under the old system bound, a retained block of arbitrary genuine labels
and a shared long pair through the same physical endpoints must use the same
old wagon, unless an actual core edge joins those endpoints.

The old four-occurrence frame is CONSTRUCTED here, not an input. -/
theorem standardPicture_block_rel_shared_of_no_core_pair
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (μ : Fin (m + 1)) (e : RelStructure.Embedding A D)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
    (i : I)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hActive : AStrong A C.toRelStructure (activeCarrier A C e.toFunctionEmbedding))
    (hFull : (standardPictureOrderOneData A B D C family T μ).FullSystemGirthGT 2)
    (a b : DesignatedCopy B D C family ⊕ OldACarrierEdge A C.toRelStructure)
    (r : OldACarrierEdge A C.toRelStructure)
    (sx sy : SharedOldACarrierEdge A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding))
    (x y : RelStructure.Attachment.Vertex
      (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I))
    (hab : a ≠ b) (hxy : x ≠ y)
    (ha : (standardPictureOrderOneData A B D C family T μ).Meets a
      (Quotient.mk (T.wagonSetoid μ) r))
    (hb : (standardPictureOrderOneData A B D C family T μ).Meets b
      (Quotient.mk (T.wagonSetoid μ) r))
    (hLong : T.rel μ sx.1 sy.1)
    (hyA : y ∈ (fun z : X => (RelStructure.Attachment.copyEmbedding
      C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i) z) ''
      (standardPictureOrderOneData A B D C family T μ).carrier a)
    (hxB : x ∈ (fun z : X => (RelStructure.Attachment.copyEmbedding
      C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i) z) ''
      (standardPictureOrderOneData A B D C family T μ).carrier b)
    (hxS : x ∈ attachedOldAEdgeCarrier A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f i sx.1)
    (hyS : y ∈ attachedOldAEdgeCarrier A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f i sy.1)
    (hNoEdge : ¬ ∃ edge : OldACarrierEdge A R,
      x ∈ attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f edge ∧
      y ∈ attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f edge) :
    T.rel μ r sx.1 := by
  let O := standardPictureOrderOneData A B D C family T μ
  let S := activeCarrier A C e.toFunctionEmbedding
  let std := RelStructure.Attachment.copyEmbedding C.toRelStructure S R f i
  by_contra hNot
  have hpq : O.parent r ≠ O.parent sx.1 := by
    intro h
    exact hNot (Quotient.exact h)
  have hef : sx.1 ≠ sy.1 := by
    intro h
    apply hNoEdge
    refine ⟨sharedOldACarrierCoreEmbedding A C.toRelStructure S R f i sx, ?_, ?_⟩
    · rw [← attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f i sx]
      exact hxS
    · rw [← attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f i sx]
      rw [show sharedOldACarrierInclusion A C.toRelStructure S sx = sy.1 from h]
      exact hyS
  change x ∈ (fun z : X => std z) '' sx.1.1 at hxS
  change y ∈ (fun z : X => std z) '' sy.1.1 at hyS
  obtain ⟨u, hu, hux⟩ := hxS
  obtain ⟨w, hw, hwy⟩ := hyS
  have huw : u ≠ w := by
    intro h
    exact hxy (hux.symm.trans ((congrArg (fun z : X => std z) h).trans hwy))
  have huB : u ∈ O.carrier b := by
    obtain ⟨z, hz, hzx⟩ := hxB
    have hzu : z = u := std.injective (hzx.trans hux.symm)
    exact hzu ▸ hz
  have hwA : w ∈ O.carrier a := by
    obtain ⟨z, hz, hzy⟩ := hyA
    have hzw : z = w := std.injective (hzy.trans hwy.symm)
    exact hzw ▸ hz
  have hParent : O.parent sy.1 = O.parent sx.1 :=
    (Quotient.sound hLong).symm
  let F : O.FourWagonFrame := OrderOneData.FourWagonFrame.of_distinct_wagons
    O a b sx.1 sy.1 (O.parent r) (O.parent sx.1) u w
    hab hef hpq huw ha hb huB hu rfl hParent hw hwA
  obtain ⟨edge, hxCore, hyCore⟩ := standardPicture_fourWagonFrame_coreEdge
    A B D C family T μ hStrong e hActive F hFull (sx.2 hu) (sy.2 hw) R f i
  apply hNoEdge
  refine ⟨edge, ?_, ?_⟩
  · change std u ∈ attachedCoreAEdgeCarrier A C.toRelStructure S R f edge at hxCore
    rwa [hux] at hxCore
  · change std w ∈ attachedCoreAEdgeCarrier A C.toRelStructure S R f edge at hyCore
    rwa [hwy] at hyCore

/-- Actual two-standard obstruction with possibly designated retained labels.
Both old frame extractions and the generated-wagon contradiction are proved;
no old frame, cross-label inequalities, or output linearity is assumed.
The two block pairs are oriented with the y-boundary first on each side. -/
theorem actualTwoStandard_designatedBlocks_force_core_pairEdge
    (A : RelStructure L UA) (hA : A.Irreducible)
    (B : RelStructure L VB) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (family : Set (RelStructure.Embedding B D))
    (e : RelStructure.Embedding A D)
    (R : RelStructure L Y)
    (f : I → RelStructure.Embedding
      (C.toRelStructure.induce (activeCarrier A C e.toFunctionEmbedding)) R)
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A C.toRelStructure) m)
    (U : EdgeTrainLevels (OldACarrierEdge A R) m)
    (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding)))
    (μ : Fin (m + 1)) (i j : I)
    (hStrong : ∀ b : RelStructure.Embedding B D, b ∈ family →
      AStrong A D (copyCarrier b))
    (hActive : AStrong A C.toRelStructure (activeCarrier A C e.toFunctionEmbedding))
    (hFull : (standardPictureOrderOneData A B D C family T μ).FullSystemGirthGT 2)
    (a b c d : DesignatedCopy B D C family ⊕ OldACarrierEdge A C.toRelStructure)
    (r s : OldACarrierEdge A C.toRelStructure)
    (x y : RelStructure.Attachment.Vertex
      (activeCarrier A C e.toFunctionEmbedding) (W := Y) (I := I))
    (hij : i ≠ j) (hxy : x ≠ y) (hab : a ≠ b) (hcd : c ≠ d)
    (ha : (standardPictureOrderOneData A B D C family T μ).Meets a
      (Quotient.mk (T.wagonSetoid μ) r))
    (hb : (standardPictureOrderOneData A B D C family T μ).Meets b
      (Quotient.mk (T.wagonSetoid μ) r))
    (hc : (standardPictureOrderOneData A B D C family T μ).Meets c
      (Quotient.mk (T.wagonSetoid μ) s))
    (hd : (standardPictureOrderOneData A B D C family T μ).Meets d
      (Quotient.mk (T.wagonSetoid μ) s))
    (hReflect : ∀ (k : I) (p q : SharedOldACarrierEdge A C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding)),
      U.rel μ (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f k p)
        (sharedOldACarrierCoreEmbedding A C.toRelStructure
          (activeCarrier A C e.toFunctionEmbedding) R f k q) →
      T.rel μ p.1 q.1)
    (hyA : y ∈ (fun z : X => (RelStructure.Attachment.copyEmbedding
      C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i) z) ''
      (standardPictureOrderOneData A B D C family T μ).carrier a)
    (hxB : x ∈ (fun z : X => (RelStructure.Attachment.copyEmbedding
      C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f i) z) ''
      (standardPictureOrderOneData A B D C family T μ).carrier b)
    (hyC : y ∈ (fun z : X => (RelStructure.Attachment.copyEmbedding
      C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f j) z) ''
      (standardPictureOrderOneData A B D C family T μ).carrier c)
    (hxD : x ∈ (fun z : X => (RelStructure.Attachment.copyEmbedding
      C.toRelStructure (activeCarrier A C e.toFunctionEmbedding) R f j) z) ''
      (standardPictureOrderOneData A B D C family T μ).carrier d)
    (hCoreLinear : (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).LinearPretrain)
    (hCoreBound : (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).LocalPieceSystemBound 2)
    (hIx : x ∈ (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).copyCarrier i)
    (hIy : y ∈ (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).copyCarrier i)
    (hJx : x ∈ (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).copyCarrier j)
    (hJy : y ∈ (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).copyCarrier j)
    (hDistinctWagons : ¬ (generatedActualASupportTrain A hA C.toRelStructure
      (activeCarrier A C e.toFunctionEmbedding) R f T U hShared).rel μ
      (actualAPictureEdgeEquiv A hA C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A C.toRelStructure
            (activeCarrier A C e.toFunctionEmbedding))
          (sharedOldACarrierCoreEmbedding A C.toRelStructure
            (activeCarrier A C e.toFunctionEmbedding) R f) i r))
      (actualAPictureEdgeEquiv A hA C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f
        (physicalStandardEdge
          (sharedOldACarrierInclusion A C.toRelStructure
            (activeCarrier A C e.toFunctionEmbedding))
          (sharedOldACarrierCoreEmbedding A C.toRelStructure
            (activeCarrier A C e.toFunctionEmbedding) R f) j s))) :
    (sharedWitnessOrderOneData U μ
      (sharedOldACarrierCoreEmbedding A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)
      (attachedCoreAEdgeCarrier A C.toRelStructure
        (activeCarrier A C e.toFunctionEmbedding) R f)).PairEdge x y := by
  let S := activeCarrier A C e.toFunctionEmbedding
  let emb := sharedOldACarrierCoreEmbedding A C.toRelStructure S R f
  let car := attachedCoreAEdgeCarrier A C.toRelStructure S R f
  by_contra hNoEdge
  obtain ⟨sx, sy, tx, ty, hLongI, hLongJ, hCross, hxsi, hysi, hxtj, hytj⟩ :=
    sharedWitness_twoCopy_common_shared_pairs U μ emb car hCoreLinear hCoreBound
      i j x y hij hxy hIx hIy hJx hJy hNoEdge
  have hSX : x ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f i sx.1 := by
    rw [attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f i sx]
    exact hxsi
  have hSY : y ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f i sy.1 := by
    rw [attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f i sy]
    exact hysi
  have hTX : x ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f j tx.1 := by
    rw [attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f j tx]
    exact hxtj
  have hTY : y ∈ attachedOldAEdgeCarrier A C.toRelStructure S R f j ty.1 := by
    rw [attachedSharedAEdgeCarrier_eq A C.toRelStructure S R f j ty]
    exact hytj
  have hOldI := standardPicture_block_rel_shared_of_no_core_pair
    A B D C family T μ e R f i hStrong hActive hFull a b r sx sy x y
    hab hxy ha hb (hReflect i sx sy hLongI) hyA hxB hSX hSY hNoEdge
  have hOldJ := standardPicture_block_rel_shared_of_no_core_pair
    A B D C family T μ e R f j hStrong hActive hFull c d s tx ty x y
    hcd hxy hc hd (hReflect j tx ty hLongJ) hyC hxD hTX hTY hNoEdge
  have hOldJ' : T.rel μ tx.1 s :=
    Quotient.exact (Quotient.sound hOldJ).symm
  exact hDistinctWagons (generatedActualASupportTrain_three_link
    A hA C.toRelStructure S R f T U hShared μ i j r s sx tx hOldI hCross hOldJ')

end StructuralRamsey.Girth
