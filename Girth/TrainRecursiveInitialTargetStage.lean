import Girth.TrainRecursiveInitialTailSystem
import Girth.TrainRecursiveRefinementReady

/-!
# Initial finite stages from the target's natural cut bounds

The actual initial tail-system girth input is now derived from ordinary
target support girth at the head and labelled target wagon-cut girth at
each positive coordinate.  The proof uses the actual initial cycle
localization and the edge-only obstruction; no output system-girth bound
is assumed.  Nonempty target support supplies the needed nonempty target
carrier, and the head bound supplies physical A-linearity.

The constructor below assembles the finite initial forest/tail stage from
these target hypotheses.  Its remaining-profile refinement readiness is
also constructed from the full active-support matching theorem.  A final
Ramsey arrow still requires the actual geometric local picture steps.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- The exact tail predicate formerly supplied to the initial-stage
constructor follows from natural target labelled cut bounds. -/
theorem initialTail_of_targetCuts
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (t : List ℕ) (ht : Admissible t)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hGirth : GirthGT (supportCopies A B) (t.headD 0))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j)) :
    ∀ j : Fin t.length, 0 < j.val →
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
          targetTrain (List.length_pos_iff.mpr ht.nonempty))
        j.castSucc).FullSystemGirthGT (t.get j) := by
  letI : Nonempty VB := by
    obtain ⟨edge⟩ := hSupportNonempty
    obtain ⟨a, _⟩ := edge.2
    obtain ⟨u⟩ := (inferInstance : Nonempty UA)
    exact ⟨a u⟩
  have hHead : 2 ≤ t.headD 0 := by
    cases t with
    | nil => exact (ht.nonempty rfl).elim
    | cons q tail => exact ht.two_le q (by simp)
  have hLinear : ALinear A B :=
    aLinear_of_girthGT_two A B (girthGT_mono hGirth hHead)
  intro j hj
  exact initialTrain_fullSystemGirth_of_targetCut A hA B D family
    targetTrain (List.length_pos_iff.mpr ht.nonempty) j.castSucc j.isLt
    (t.get j) (ht.two_le _ (List.get_mem t j)) hLinear (hTargetCuts j hj)

/-- A genuine finite selected initial stage from target support, allowed
parts and natural horizontal-cut girth.  No initial output tail or ready
stage is supplied as a hypothesis. -/
noncomputable def initialForestTailStage_of_targetCuts
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
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
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j)) :
    ForestTailStage A B D family t targetTrain allowed :=
  initialForestTailStage_of_tail A hA B D family t ht targetTrain allowed
    hSupportNonempty hSupportCovers hGirth hTargetParameters
    (initialTail_of_targetCuts A hA B D family t ht targetTrain
      hSupportNonempty hGirth hTargetCuts)

/-- The target-cut constructor is ready for the finite pass at every
finite refinement budget and every remaining profile list. -/
theorem initialForestTailStage_of_targetCuts_firstRefinementReady
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
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun edge => edge.1) j.castSucc)
        (t.get j))
    (q : ℕ) (profiles : List (UA ↪ P)) :
    ForestTailStage.FirstRefinementReady (List.length_pos_iff.mpr ht.nonempty)
      q profiles
      (initialForestTailStage_of_targetCuts A hA B D family t ht targetTrain allowed
        hSupportNonempty hSupportCovers hGirth hTargetParameters hTargetCuts) := by
  exact initialForestTailStage_firstRefinementReady A hA B D family t ht
    targetTrain allowed hSupportNonempty hSupportCovers hGirth hTargetParameters
    (initialTail_of_targetCuts A hA B D family t ht targetTrain
      hSupportNonempty hGirth hTargetCuts) q profiles

end StructuralRamsey.Girth.TrainRecursiveWitness
