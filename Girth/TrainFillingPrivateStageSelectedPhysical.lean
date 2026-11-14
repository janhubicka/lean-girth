import Girth.TrainFillingIndexedActualMPhysicalTrain

set_option Elab.async false

/-!
# One actual shorter-stage selected copy gives the full old-edge map

No independent embedding of the contracted edge labels (choice, first
wagon) is allowed in the cutoff-two application. The lower recursive
witness already returns a genuine selected relational M-copy b in its
ForestTailStage.

The previous checked modules give its entire physical old-edge
embedding and train-relation reflection. This file packages those
results as ONE joint existential witness, with an exact full-carrier
equation for every contracted first wagon. In particular, the actual
chosen b is the same in the carrier and all-cut relation conclusions.

The next application transports this old-edge map into the canonical
filled edge equivalence of N[X] and then constructs all parentwise
realization fields. No ambient-edge deletion, extra output girth or
unconstructed Ramsey arrow is assumed.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {C V P X UA : Type v}
variable (U : C → PrivateWagonInput V P X)

/-- Exact full physical carrier of every selected old M-edge from
the genuine relational selected b. -/
theorem stageSelectedActualMPhysicalEdge_carrier [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family)
    (cp : C × P) :
    (selectedActualMPhysicalEdgeEmbedding U A M T hm
      hSupport hLinear D family allowed S b cp).1 =
      b.embedding.toFunctionEmbedding '' contractedCarrier U cp := by
  change b.embedding.toFunctionEmbedding ''
      (contractedPhysicalEdgeEquiv U A M hSupport hLinear cp).1 =
    b.embedding.toFunctionEmbedding '' contractedCarrier U cp
  rw [contractedPhysicalEdgeEquiv_carrier]

/-- The actual stage b produces one physical edge map which is
simultaneously exact on complete carriers and faithful at EVERY train
cut. No separate β or hFaithful is supplied as a hypothesis. -/
theorem exists_stageSelectedActualMPhysicalFaithful [Nontrivial X]
    (A : RelStructure L UA)
    (M : RelStructure L (Vertex U))
    {t : List ℕ} (T : EdgeTrainLevels P t.length) (hm : 0 < t.length)
    (hSupport : supportCopies A M = Set.range (contractedCarrier U))
    (hLinear : ∀ c : C, ∀ p q : P, p ≠ q →
      ((U c).oldCarrier p ∩ (U c).oldCarrier q).Subsingleton)
    {Base : Type v} (D : RelStructure L Base)
    (family : Set (Embedding M D))
    (allowed : Fin (t.length + 1) → Set Base)
    (S : TrainRecursiveWitness.ForestTailStage A M D family t
      (contractedPhysicalTrain U A M T hm hSupport hLinear) allowed)
    (b : DesignatedCopy M D S.system family)
    (hb : b ∈ S.selected) :
    ∃ (β : (C × P) ↪ OldACarrierEdge A S.system.toRelStructure),
      (∀ cp : C × P, (β cp).1 =
        b.embedding.toFunctionEmbedding '' contractedCarrier U cp) ∧
      (∀ (μ : Fin (t.length + 1)) (e f : C × P),
        (contractedChoiceTrain U T hm).rel μ e f ↔
          S.train.rel μ (β e) (β f)) := by
  let β := selectedActualMPhysicalEdgeEmbedding
    U A M T hm hSupport hLinear D family allowed S b
  refine ⟨β, ?_, ?_⟩
  · intro cp
    exact stageSelectedActualMPhysicalEdge_carrier
      U A M T hm hSupport hLinear D family allowed S b cp
  · intro μ e f
    exact (selectedActualMPhysicalEdgeEmbedding_train_iff
      U A M T hm hSupport hLinear D family allowed S b hb μ e f).symm

end StructuralRamsey.Girth.IndexedPrivateChoice
