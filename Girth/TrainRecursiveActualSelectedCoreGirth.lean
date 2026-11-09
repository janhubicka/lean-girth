import Girth.TrainRecursiveActualCoarsenedFullRecursiveCutoffs
import Girth.TrainRecursiveFineWitnessBounds
import Girth.TrainRecursiveCanonicalFineParametersCast
import Girth.TrainRecursiveSelectedWitnessConsequences
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
# Real selected lower stage gives physical coarsened core girth > q

All physical A-support edges and the literal selected designated-copy
subtype survive coarsening. The actual lower ForestTailStage provides:
(i) complete selected mixed bottom forest through q-1;
(ii) all fine adjacent parameters, transported through the genuine
height equality;
(iii) complete positive physical FullSystemGirthGT at inserted q-1
and retained q cuts, from its selected tailGirth and the already
audited physical incidence equivalence.

Apply the checked intrinsic first-wagon physical girth-gain theorem.
The ONLY remaining geometric premise is singleton fine A-parts at
the inserted parents; the genuine FirstWagonRefinement will supply
it via its canonical permitted sets in a separate specialization.

No new axiom, invented lower stage, omitted ambient edge, unindexed
selection or assumed output SupremeCycleBound. This is circulation-only.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P V X : Type v}

private theorem actualCoreLowerHeight (q r : ℕ) (tail : List ℕ) :
    (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length := by
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

/-- A genuine selected lower ForestTailStage, with its exact
part-preserving gluing family and canonical lower train, forces
ordinary girth > q of the COMPLETE coarsened physical A-support.
There is NO independently assumed mixed forest, adjacent parameter,
or system-girth field: all three come from the actual lower stage. -/
theorem ForestTailStage.coarsenedSelected_coreGirth_from_actualLower
    (A : RelStructure L UA) (hA : A.Irreducible)
    (Old : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P)
    (D : StructuralRamsey.Partite.System L UA V)
    {q r : ℕ} {tail : List ℕ}
    {family : Set (Embedding
      (Old.toRelStructure.induce (activeCarrier A Old α))
      D.toRelStructure)}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A
        (Old.toRelStructure.induce (activeCarrier A Old α)))
      (List.replicate (r + 1) (q - 1) ++ tail).length}
    (fineAllowed :
      Fin ((List.replicate (r + 1) (q - 1) ++ tail).length + 1) → Set UA)
    (S : ForestTailStage A
      (Old.toRelStructure.induce (activeCarrier A Old α))
      D.toRelStructure family
      (List.replicate (r + 1) (q - 1) ++ tail) targetTrain
      (fun ν => D.part ⁻¹' fineAllowed ν))
    (hFamilyParts : ∀ b, b ∈ family →
      ∀ x : activeCarrier A Old α,
        D.part (b x) = activeSourcePart A Old α x)
    (hq : 2 < q)
    (hMonotone : (q :: tail).Pairwise (· ≤ ·))
    (hSingleton : ∀ j : Fin (r + 1),
      (fineAllowed (Fin.cast
        (congrArg (fun k : ℕ => k + 1)
          (actualCoreLowerHeight q r tail))
        (firstRefinementParent (q :: tail).length r
          (by simp : 0 < (q :: tail).length) j))).Subsingleton) :
    GirthGT (supportCopies A
      (S.system.coarsenVia D S.isPartite).toRelStructure) q := by
  classical
  let Target := actualActiveSubsystemPartite A Old α
  let E := S.system.coarsenVia D S.isPartite
  let I := {b : DesignatedCopy
    (Old.toRelStructure.induce (activeCarrier A Old α))
    D.toRelStructure S.system family // b ∈ S.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target D S.system S.isPartite family hFamilyParts S.selected i
  have hm : 0 < (q :: tail).length := by simp
  have hLen : (q :: tail).length + r =
      (List.replicate (r + 1) (q - 1) ++ tail).length :=
    actualCoreLowerHeight q r tail
  let T := S.train.castHeight hLen.symm
  let actualFineAllowed : Fin ((q :: tail).length + r + 1) → Set UA :=
    fun ν => fineAllowed
      (Fin.cast (congrArg (fun k : ℕ => k + 1) hLen) ν)
  have hParameters :
      T.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' actualFineAllowed ν) :=
    S.coarsened_adjacentParameters_castHeight_preimage
      A (Old.toRelStructure.induce (activeCarrier A Old α))
      D fineAllowed hLen
  have hHead :
      (List.replicate (r + 1) (q - 1) ++ tail).headD 0 = q - 1 := by
    simp [List.replicate_succ]
  have hForest : FiniteMixedForestThrough
      (RelationalMixedSupportTest A
        (fun i : I => (f i).toEmbedding)) (q - 1) := by
    apply S.selectedEmbeddings_mixedForest
      (fun i : I => (f i).toEmbedding)
      ?_ (q - 1) (by simpa only [hHead] using Nat.le_refl (q - 1))
    intro i
    exact ⟨i.1, i.2, rfl⟩
  have hFull : ∀ ν : Fin ((q :: tail).length + r + 1),
      0 < ν.val → ν.val < (q :: tail).length + r →
      (activeGluingWitnessOrderOneData A Old α E.toRelStructure
        (fun i : I => (f i).toEmbedding) T ν).FullSystemGirthGT
          (if ν.val ≤ r then q - 1 else q) := by
    intro ν hPos hInterior
    exact S.coarsenedSelected_fullSystem_for_attachmentHeight
      A Old α D hFamilyParts hLen rfl hMonotone ν hPos hInterior
  exact activeFineWitness_supportGirth
    A hA Old α E f hm hq T actualFineAllowed
    hParameters hSingleton hForest hFull

end StructuralRamsey.Girth.TrainRecursiveWitness
