import Girth.TrainRecursiveWitnessPass
import Girth.ForestSelectedMixedCoverage
import Girth.ForestRecursiveOutputGirth
import Girth.TrainFullGirthCopyStrongness
import Girth.TrainEndpointGeometry

set_option Elab.async false

/-!
# Bottom forest invariants of an intrinsic recursive attachment

The old recursive stage already tests every ambient A-edge and precisely
its selected B-supports.  The actual forest increment can therefore consume
`stage.bottomForest` directly.  Its output tests precisely the canonical
transports of those selected copies, as expressed by `testedAB`.

At the cutoff-two forest step, an intrinsic local system-girth bound at
any supplied cut, with numerical bound at least two, supplies strongness
of every whole gluing image.
At larger bottom cutoffs the predecessor mixed forest already supplies
that strongness, so no intrinsic cycle bound is requested again.  The
existing actual attachment theorem derives ordinary output girth greater
than two before applying the forest increment; output geometry is not
assumed.

The genuine higher-cutoff core ordinary girth bound and the local mixed
forest bound through its predecessor remain explicit.  At bottom cutoff
two, the same intrinsic bound already gives core physical linearity and
hence core ordinary girth greater than two.  The result supplies the output
bottom forest, ordinary support girth, and strongness of each canonical
selected B-copy.  It asserts neither local Ramsey existence nor any output
tail system-girth condition.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}} {UA VB P X Y I : Type v}

/-- The recursive tested-piece predicate for the canonical output
selection is exactly the physical predicate used by the forest increment.
No injectivity or choice of physical representatives is needed here. -/
theorem testedAB_transportedSelectedCopies_iff
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (C : StructuralRamsey.Partite.System L P X)
    (family : Set (Embedding B D))
    (selected : Set (DesignatedCopy B D C family))
    (S : Set X) (E : StructuralRamsey.Partite.System L P Y)
    (f : I → StructuralRamsey.Partite.Embedding (C.induce S) E)
    (piece : HypergraphPiece
      (StructuralRamsey.Partite.Attachment.Vertex S (W := Y) (I := I))) :
    testedAB A B D (StructuralRamsey.Partite.Attachment.attach C S E f)
      family (transportedSelectedCopies B D C family selected S E f) piece ↔
      (∃ a : Embedding A
        (StructuralRamsey.Partite.Attachment.attach C S E f).toRelStructure,
        piece = HypergraphPiece.oneEdge (copyCarrier a)) ∨
      (∃ i : I, ∃ b : DesignatedCopy B D C family, b ∈ selected ∧
        piece = bSupportPiece A (b.transportToStandard f i).embedding) := by
  constructor
  · rintro (hA | ⟨b, ⟨i, old, hOld, rfl⟩, hPiece⟩)
    · exact Or.inl hA
    · exact Or.inr ⟨i, old, hOld, hPiece⟩
  · rintro (hA | ⟨i, old, hOld, hPiece⟩)
    · exact Or.inl hA
    · exact Or.inr ⟨old.transportToStandard f i, ⟨i, old, hOld, rfl⟩, hPiece⟩

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- A supplied intrinsic local witness preserves the actual old stage's
bottom forest on the canonical transported selected family.  Whole-image
strongness and ambient output girth greater than two are derived inputs.
The local predecessor forest and higher-cutoff core ordinary girth are
retained; at cutoff two the intrinsic bound supplies core girth as well. -/
theorem ForestTailStage.activeAttachment_bottom_invariants_of_intrinsic
    (stage : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) [Finite UA]
    (hBaseLinear : ALinear A D)
    (e : Embedding A D)
    (hRigid : ∀ a : Embedding A D, SameCopy a e → a = e)
    (hActive : (activeCarrier A stage.system e.toFunctionEmbedding).Nonempty)
    (E : StructuralRamsey.Partite.System L P Y) [Finite Y]
    (f : I → StructuralRamsey.Partite.Embedding
      (stage.system.induce (activeCarrier A stage.system e.toFunctionEmbedding)) E)
    (hBaseStrong : ∀ b : DesignatedCopy B D stage.system family, b ∈ stage.selected →
      AStrong A D (copyCarrier b.base))
    (hk : 2 ≤ t.headD 0)
    (hLocal : t.headD 0 = 2 ∨
      ((∃ e₀ e₁ : Set (activeCarrier A stage.system e.toFunctionEmbedding),
          e₀ ∈ supportCopies A
            (stage.system.induce
              (activeCarrier A stage.system e.toFunctionEmbedding)).toRelStructure ∧
          e₁ ∈ supportCopies A
            (stage.system.induce
              (activeCarrier A stage.system e.toFunctionEmbedding)).toRelStructure ∧
          e₀ ≠ e₁) ∧
        Function.Injective (fun i => bSupportPiece A (f i).toEmbedding) ∧
        FiniteMixedForestThrough
          (RelationalMixedSupportTest A (fun i => (f i).toEmbedding)) (t.headD 0 - 1)))
    (hCoreGirth : 2 < t.headD 0 →
      GirthGT (supportCopies A E.toRelStructure) (t.headD 0))
    (U : EdgeTrainLevels (OldACarrierEdge A E.toRelStructure) t.length)
    (hTwoBound : t.headD 0 = 2 →
      ∃ μ : Fin (t.length + 1), ∃ q : ℕ, 2 ≤ q ∧
        (activeGluingWitnessOrderOneData A stage.system e.toFunctionEmbedding
          E.toRelStructure (fun i => (f i).toEmbedding) U μ).FullSystemGirthGT q) :
    let S := activeCarrier A stage.system e.toFunctionEmbedding
    let attached := StructuralRamsey.Partite.Attachment.attach stage.system S E f
    let selected := transportedSelectedCopies B D stage.system family stage.selected S E f
    FiniteMixedForestThrough (testedAB A B D attached family selected) (t.headD 0) ∧
      GirthGT (supportCopies A attached.toRelStructure) (t.headD 0) ∧
      ∀ b : DesignatedCopy B D attached family, b ∈ selected →
        AStrong A attached.toRelStructure (copyCarrier b.embedding) := by
  classical
  let : Fintype Y := Fintype.ofFinite Y
  let S := activeCarrier A stage.system e.toFunctionEmbedding
  let attached := StructuralRamsey.Partite.Attachment.attach stage.system S E f
  let selected := transportedSelectedCopies B D stage.system family stage.selected S E f
  change FiniteMixedForestThrough (testedAB A B D attached family selected) (t.headD 0) ∧
    GirthGT (supportCopies A attached.toRelStructure) (t.headD 0) ∧
    ∀ b : DesignatedCopy B D attached family, b ∈ selected →
      AStrong A attached.toRelStructure (copyCarrier b.embedding)
  have hTwoGeometry : t.headD 0 = 2 →
      ALinear A E.toRelStructure ∧
        ∀ i, AStrong A E.toRelStructure (copyCarrier (f i).toEmbedding) := by
    intro hTwo
    obtain ⟨μ, q, hq, hFull⟩ := hTwoBound hTwo
    refine ⟨aLinear_of_oldACarrier_edges_inter_subsingleton A E.toRelStructure
      hFull.1.1, ?_⟩
    exact activeGluingWitness_images_aStrong_of_fullSystemGirth
      A stage.system e.toFunctionEmbedding E.toRelStructure
      (fun i => (f i).toEmbedding) U μ q hq hFull
  have hCore : GirthGT (supportCopies A E.toRelStructure) (t.headD 0) := by
    by_cases hTwo : t.headD 0 = 2
    · rw [hTwo]
      exact girthGT_two_of_aLinear A E.toRelStructure (hTwoGeometry hTwo).1
    · exact hCoreGirth (by omega)
  have hRaw := actualPartiteDesignatedAB_forest_and_girth_of_localGeometry
    A hA B D stage.system stage.isPartite hBaseLinear family stage.selected
    e hRigid hActive E f hBaseStrong (t.headD 0) hk
    (fun hTwo => (hTwoGeometry hTwo).2) hLocal hCore
    (testedAB A B D stage.system family stage.selected) stage.bottomForest
    (fun a => Or.inl ⟨a, rfl⟩)
    (fun b hb => Or.inr ⟨b, hb, rfl⟩)
  have hForest : FiniteMixedForestThrough
      (testedAB A B D attached family selected) (t.headD 0) := by
    intro s hs hCard
    apply hRaw.1 s ?_ hCard
    intro piece hPiece
    exact (testedAB_transportedSelectedCopies_iff A B D stage.system family
      stage.selected S E f piece).mp (hs piece hPiece)
  refine ⟨hForest, hRaw.2, ?_⟩
  intro b hb
  exact aStrong_of_finiteMixedForestThrough A b.embedding
    (testedAB A B D attached family selected) (t.headD 0) hk hForest
    (Or.inr ⟨b, hb, rfl⟩) (fun a => Or.inl ⟨a, rfl⟩)

end StructuralRamsey.Girth.TrainRecursiveWitness
