import Girth.TrainRecursiveInitialTargetStage

/-!
# Complete recursive witnesses for a one-physical-edge target

For a target whose complete A-support consists of one physical edge, every
train cut has at most one wagon label.  Its labelled cut girth is therefore
arbitrarily large, and every allowed-part parameter holds.  These facts are
proved from the physical support condition, without a local Ramsey operator.

The witness is the actual initial picture over the singleton identity base
family.  The target-cut construction supplies its finite forest/tail stage;
the same actual initial system-girth theorem supplies the bottom cut as well.
For a finite ordered source, all embeddings into the target are equal by
ordered-source rigidity.  The literal selected identity-component copy is
thus monochromatic for every colouring, with no assumption on the colour
type.  Target support nonemptiness and coverage remain explicit.
-/

namespace StructuralRamsey.Girth

universe u v w
variable {L : RelLanguage.{u}} {UA VB : Type v}

/-- A subsingleton family of physical support carriers gives a subsingleton
actual edge type.  Embeddings themselves need not be subsingleton here. -/
theorem oldACarrierEdge_subsingleton_of_support_subsingleton
    (A : RelStructure L UA) (B : RelStructure L VB)
    (hPhysical : (supportCopies A B).Subsingleton) :
    Subsingleton (OldACarrierEdge A B) := by
  refine ⟨fun e f => Subtype.ext ?_⟩
  exact hPhysical e.property f.property

/-- Every labelled target cut, including the top, has arbitrary girth when
there is at most one actual physical support edge. -/
theorem oneEdgeTarget_labelledCutGirth
    (A : RelStructure L UA) (B : RelStructure L VB)
    (hPhysical : (supportCopies A B).Subsingleton)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m)
    (μ : Fin (m + 1)) (q : ℕ) :
    LabelledGirthGT (T.wagonClassCarrier (fun edge => edge.1) μ) q := by
  letI : Subsingleton (OldACarrierEdge A B) :=
    oldACarrierEdge_subsingleton_of_support_subsingleton A B hPhysical
  exact T.labelledCutGirth_of_matching (fun edge => edge.1)
    (fun {_ _} hne => (hne (Subsingleton.elim _ _)).elim) μ q

/-- A one-physical-edge target satisfies every adjacent parameter, for
arbitrary allowed vertex sets and the original train at every level. -/
theorem oneEdgeTarget_adjacentParameters
    (A : RelStructure L UA) (B : RelStructure L VB)
    (hPhysical : (supportCopies A B).Subsingleton)
    {m : ℕ} (T : EdgeTrainLevels (OldACarrierEdge A B) m)
    (allowed : Fin (m + 1) → Set VB) :
    T.AdjacentParameters (fun edge => edge.1) allowed := by
  letI : Subsingleton (OldACarrierEdge A B) :=
    oldACarrierEdge_subsingleton_of_support_subsingleton A B hPhysical
  exact T.adjacentParameters_of_matching (fun edge => edge.1)
    (fun {_ _} hne => (hne (Subsingleton.elim _ _)).elim) allowed

namespace TrainRecursiveWitness

/-- A complete finite order stage for a covered one-physical-edge target.
The base is the target itself and the base family is its singleton identity
embedding.  No initial tail bound, parameter bound, or local step is assumed.
-/
noncomputable def oneEdgeTargetOrderStage
    (A₀ : RelStructure L UA) [LinearOrder UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hPhysical : (supportCopies A₀.ordered B).Subsingleton)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A₀.ordered B, b ∈ e.1) :
    OrderStage A₀.ordered B B {RelStructure.Embedding.id B} t targetTrain allowed := by
  let family : Set (RelStructure.Embedding B B) := {RelStructure.Embedding.id B}
  letI : Nonempty family := ⟨⟨RelStructure.Embedding.id B, rfl⟩⟩
  letI : Nonempty VB := by
    obtain ⟨edge⟩ := hSupportNonempty
    obtain ⟨a, _⟩ := edge.2
    obtain ⟨u⟩ := (inferInstance : Nonempty UA)
    exact ⟨a u⟩
  have hA : A₀.ordered.Irreducible :=
    (RelStructure.ordered_hereditarilyIrreducible A₀).irreducible
  have hGirth : GirthGT (supportCopies A₀.ordered B) (t.headD 0) :=
    girthGT_of_edgeFamily_subsingleton hPhysical (t.headD 0)
  let S := initialForestTailStage_of_targetCuts A₀.ordered hA B B family t ht
    targetTrain allowed hSupportNonempty hSupportCovers hGirth
    (fun b => oneEdgeTarget_adjacentParameters A₀.ordered B hPhysical
      targetTrain (fun ν => b.1 ⁻¹' allowed ν))
    (fun j _ => oneEdgeTarget_labelledCutGirth A₀.ordered B hPhysical
      targetTrain j.castSucc (t.get j))
  refine { toForestTailStage := S, allCutGirth := ?_ }
  intro j
  exact initialTrain_fullSystemGirth_of_targetCut A₀.ordered hA B B family
    targetTrain (List.length_pos_iff.mpr ht.nonempty) j.castSucc j.isLt
    (t.get j) (ht.two_le _ (List.get_mem t j))
    (aLinear_of_girthGT_two A₀.ordered B
      (girthGT_of_edgeFamily_subsingleton hPhysical 2))
    (oneEdgeTarget_labelledCutGirth A₀.ordered B hPhysical
      targetTrain j.castSucc (t.get j))

/-- The actual selected identity-component copy in the one-edge stage is
monochromatic.  Ordered-source rigidity supplies equality of all target
A-embeddings, so the colour type may be arbitrary. -/
theorem oneEdgeTargetOrderStage_designatedArrow
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hPhysical : (supportCopies A₀.ordered B).Subsingleton)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A₀.ordered B, b ∈ e.1)
    (κ : Type w) :
    DesignatedArrow
      (oneEdgeTargetOrderStage A₀ B t ht targetTrain allowed
        hPhysical hSupportNonempty hSupportCovers).toForestTailStage κ := by
  intro χ
  let b : ({RelStructure.Embedding.id B} : Set (RelStructure.Embedding B B)) :=
    ⟨RelStructure.Embedding.id B, rfl⟩
  refine ⟨initialDesignatedCopy B B {RelStructure.Embedding.id B} b, ⟨b, rfl⟩, ?_⟩
  intro a₁ a₂
  have hSame : SameCopy a₁ a₂ := hPhysical ⟨a₁, rfl⟩ ⟨a₂, rfl⟩
  have hEq : a₁ = a₂ := ordered_embedding_eq_of_sameCopy a₁ a₂ hSame
  rw [hEq]

/-- The complete one-physical-edge target case: an actual finite order
stage and its selected strong train Ramsey arrow at every admissible vector.
All stage fields and the arrow belong to the same constructed witness. -/
theorem exists_orderStage_designatedArrow_of_oneEdgeTarget
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (B : RelStructure L.withOrder VB) [Finite VB]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A₀.ordered B) t.length)
    (allowed : Fin (t.length + 1) → Set VB)
    (hPhysical : (supportCopies A₀.ordered B).Subsingleton)
    (hSupportNonempty : Nonempty (OldACarrierEdge A₀.ordered B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A₀.ordered B, b ∈ e.1)
    (κ : Type w) :
    ∃ S : OrderStage A₀.ordered B B {RelStructure.Embedding.id B}
        t targetTrain allowed,
      DesignatedArrow S.toForestTailStage κ := by
  exact ⟨oneEdgeTargetOrderStage A₀ B t ht targetTrain allowed
    hPhysical hSupportNonempty hSupportCovers,
    oneEdgeTargetOrderStage_designatedArrow A₀ B t ht targetTrain allowed
      hPhysical hSupportNonempty hSupportCovers κ⟩

end TrainRecursiveWitness
end StructuralRamsey.Girth
