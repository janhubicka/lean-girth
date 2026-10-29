import Girth.TrainRecursiveRefinementInitial
import Girth.TrainRecursiveWitnessInitialStage

/-!
# Constructed refinement readiness of the actual initial stage

This specializes the complete-active-support refinement construction to the
finite stage used by the selected Ramsey pass.  The readiness predicate is
the existence of the manuscript's finite first-wagon refinements for each
remaining profile, with labelled child girth and at-most-singleton allowed
parts.  Its initial proof and its profile-drop law are supplied here.

An attachment step must still construct the next stage and preserve this
predicate on its remaining profiles.  The theorem below neither assumes nor
supplies such a local Ramsey step.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

namespace ForestTailStage

/-- A concrete readiness predicate in the exact argument order consumed by
`finitePass`: the remaining active trains admit finite refinements. -/
def FirstRefinementReady
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (RelStructure.Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    (ht : 0 < t.length) (q : ℕ) (profiles : List (UA ↪ P))
    (S : ForestTailStage A B D family t targetTrain allowed) : Prop :=
  RemainingFirstRefinable A S.system S.train ht
    (allowed ⟨1, Nat.succ_lt_succ ht⟩) q profiles

/-- This readiness invariant has a proved drop law, usable in particular
when an absent profile is processed by the identity picture step. -/
theorem FirstRefinementReady.tail
    {A : RelStructure L UA} {B : RelStructure L VB}
    {D : RelStructure L P} {family : Set (RelStructure.Embedding B D)}
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
    {allowed : Fin (t.length + 1) → Set P}
    {ht : 0 < t.length} {q : ℕ} {α : UA ↪ P} {profiles : List (UA ↪ P)}
    {S : ForestTailStage A B D family t targetTrain allowed}
    (h : FirstRefinementReady ht q (α :: profiles) S) :
    FirstRefinementReady ht q profiles S :=
  RemainingFirstRefinable.tail h

end ForestTailStage

/-- The actual initial finite forest/tail stage is ready at every finite
refinement-girth budget.  This discharges its initial readiness input from
the target data rather than postulating a refinement or a ready stage.
-/
theorem initialForestTailStage_firstRefinementReady
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA] [Finite UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (allowed : Fin (t.length + 1) → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν))
    (hInitialTail : ∀ j : Fin t.length, 0 < j.val →
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
          targetTrain (List.length_pos_iff.mpr ht.nonempty))
        j.castSucc).FullSystemGirthGT (t.get j))
    (q : ℕ) (profiles : List (UA ↪ P)) :
    ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
      q profiles
      (initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hInitialTail) := by
  exact initial_remainingFirstRefinable A hA B
    (fun b : family => b.1.toFunctionEmbedding)
    (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
      targetTrain (List.length_pos_iff.mpr ht.nonempty))
    (List.length_pos_iff.mpr ht.nonempty) _ q profiles

end StructuralRamsey.Girth.TrainRecursiveWitness
