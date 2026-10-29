import Girth.TrainRecursiveWitnessInitialParameters
import Girth.ForestRecursiveInitialMixed
import Girth.InitialForestCompletion

/-!
# The actual initial forest/tail stage

This constructor assembles the finite initial picture used by the recursive
pass from the target's actual support data.  Target support girth supplies
A-linearity and the complete selected-B / ambient-A mixed forest.  Literal
components supply selected membership, physical distinctness, strongness,
irreducible coverage and exact target-train restriction.  Target adjacent
parameters lift through the actual initial train.

The only remaining initial output bound supplied as an input is the exact
tail system-girth statement.  Its picture-zero proof still needs localization
and target horizontal-cut exclusion of edge-only cycles.  No whole output
stage or remaining-fibre readiness predicate is assumed.  Nonempty target
support and coverage of its vertices are explicit hypotheses.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- Build the actual finite selected initial stage, conditional only on its
explicit tail-cycle input beyond the stated target hypotheses. -/
noncomputable def initialForestTailStage_of_tail
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
    (hInitialTail : ∀ j : Fin t.length, 0 < j.val →
      (selectedPictureOrderOneData A B D
        (StructuralRamsey.Partite.Initial.picture B
          (fun b : family => b.1.toFunctionEmbedding))
        family (initialSelected B D family)
        (initialTrain A hA B (fun b : family => b.1.toFunctionEmbedding)
          targetTrain (List.length_pos_iff.mpr ht.nonempty))
        j.castSucc).FullSystemGirthGT (t.get j)) :
    ForestTailStage A B D family t targetTrain allowed := by
  have hHead : 2 ≤ t.headD 0 := by
    cases t with
    | nil => exact (ht.nonempty rfl).elim
    | cons q tail => exact ht.two_le q (by simp)
  have hLinear : ALinear A B :=
    aLinear_of_girthGT_two A B (girthGT_mono hGirth hHead)
  letI : Nonempty VB := by
    obtain ⟨edge⟩ := hSupportNonempty
    obtain ⟨a, _⟩ := edge.2
    obtain ⟨u⟩ := (inferInstance : Nonempty UA)
    exact ⟨a u⟩
  let β : family → VB ↪ P := fun b => b.1.toFunctionEmbedding
  let hm : 0 < t.length := List.length_pos_iff.mpr ht.nonempty
  refine {
    Vertex := family × VB
    finiteVertex := inferInstance
    system := StructuralRamsey.Partite.Initial.picture B β
    isPartite := StructuralRamsey.Partite.Induced.Initial.picture_isPartiteOver
      B D (fun b : family => b.1)
    aLinear := initialPicture_aLinear A hA B β hLinear
    supportNonempty := initial_supportNonempty A B β hSupportNonempty
    supportCovers := initial_supportCovers A B β hSupportCovers
    selected := initialSelected B D family
    selectedPhysicalInjective := initialSelected_physical_injective A B D family
    mixedCoverage := ?_
    strong := initialSelected_strong A B D family hA
    train := initialTrain A hA B β targetTrain hm
    targetRestriction := initialSelected_targetRestriction A B D family hA
      targetTrain hm
    parameters := initialTrain_adjacentParameters A hA B β targetTrain hm
      allowed hTargetParameters
    bottomForest := initialSelected_mixedForest A hA B D family
      (t.headD 0) hHead hGirth
    tailGirth := hInitialTail
  }
  intro S hS
  exact Or.inl (initialSelected_mixedCoverage B D family S hS)

/-- The genuine initial forest stage at a single cutoff has no tail-cycle
obligation.  In particular `q = 2` gives an actual initial stage at `[2]`.
This is the initial picture; the Ramsey arrow still requires the finite pass.
-/
noncomputable def initialForestStage_singleton
    (A : RelStructure L UA) (hA : A.Irreducible) [Nonempty UA]
    (B : RelStructure L VB) [Finite VB]
    (D : RelStructure L P) [Finite P]
    (family : Set (RelStructure.Embedding B D)) [Nonempty family]
    (q : ℕ) (hq : 2 ≤ q)
    (targetTrain : EdgeTrainLevels (OldACarrierEdge A B) 1)
    (allowed : Fin 2 → Set P)
    (hSupportNonempty : Nonempty (OldACarrierEdge A B))
    (hSupportCovers : ∀ b : VB, ∃ e : OldACarrierEdge A B, b ∈ e.1)
    (hGirth : GirthGT (supportCopies A B) q)
    (hTargetParameters : ∀ b : family,
      targetTrain.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' allowed ν)) :
    ForestTailStage A B D family [q] targetTrain allowed := by
  have ht : Admissible [q] := by
    refine ⟨by simp, by simp, ?_⟩
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact hq
  apply initialForestTailStage_of_tail A hA B D family [q] ht
    targetTrain allowed hSupportNonempty hSupportCovers hGirth hTargetParameters
  intro j hj
  have hlt : j.val < 1 := j.isLt
  omega

end StructuralRamsey.Girth.TrainRecursiveWitness
