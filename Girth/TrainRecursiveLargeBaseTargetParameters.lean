import Girth.TrainRecursiveLargeBaseCutParameters
import Girth.TrainRecursiveLargeBasePartiteInput

set_option autoImplicit false
set_option Elab.async false

/-!
# Target train parameters pulled back along genuine large-base embeddings

The q>2 lower forest-stage invocation starts with an A-partite
TARGET (the true active source) and a larger A-partite Hales--Jewett
Ramsey base. Its INITIAL target-train parameter hypothesis is
required for each selected BASE embedding b of the target into
the larger base, not only after the lower witness is built.

If b preserves the original A-parts, the preimage of
D.part^{-1}(fineAllowed nu) under b is LITERALLY the preimage of
fineAllowed nu under Target.part. Consequently the true active
target's AdjacentParameters proof supplies ALL selected base
embeddings' required initial parameter inputs.

This is the forward initialization companion of the checked
coarsened lower-stage parameter transport. It preserves all
physical support edges and quotient wagon labels. It does NOT
construct the lower ForestTailStage or its positive system-girth
or attached-output SupremeCycleBound. Circulation only.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA VB P : Type v}

/-- One actual A-part-preserving target embedding pulls the chosen
larger-base permitted parts back to EXACTLY the source A-parts.
No extra train, carrier or edge hypothesis is required. -/
theorem EdgeTrainLevels.adjacentParameters_of_largeBasePartEmbedding
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA VB)
    (D : StructuralRamsey.Partite.System L UA P)
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) m)
    (fineAllowed : Fin (m + 1) → Set UA)
    (hTarget : T.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' fineAllowed ν))
    (b : Embedding Target.toRelStructure D.toRelStructure)
    (hParts : ∀ x : VB, D.part (b x) = Target.part x) :
    T.AdjacentParameters (fun edge => edge.1)
      (fun ν => b ⁻¹' (D.part ⁻¹' fineAllowed ν)) := by
  have hSets :
      (fun ν : Fin (m + 1) =>
        b ⁻¹' (D.part ⁻¹' fineAllowed ν)) =
      (fun ν : Fin (m + 1) =>
        Target.part ⁻¹' fineAllowed ν) := by
    funext ν
    ext x
    simp only [Set.mem_preimage, hParts x]
  rw [hSets]
  exact hTarget

/-- The same initialization parameters are inherited simultaneously
by the COMPLETE prescribed large-base copy family. In the lower
initial-stage constructor this is the literal
  ∀ b : family, targetTrain.AdjacentParameters ...
premise, with allowed P-parts chosen as the inverse images of the
fine allowed A-parts. -/
theorem EdgeTrainLevels.adjacentParameters_of_largeBaseFamily
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA VB)
    (D : StructuralRamsey.Partite.System L UA P)
    {m : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A Target.toRelStructure) m)
    (fineAllowed : Fin (m + 1) → Set UA)
    (hTarget : T.AdjacentParameters (fun edge => edge.1)
      (fun ν => Target.part ⁻¹' fineAllowed ν))
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x) :
    ∀ b : family,
      T.AdjacentParameters (fun edge => edge.1)
        (fun ν => b.1 ⁻¹' (D.part ⁻¹' fineAllowed ν)) := by
  intro b
  exact T.adjacentParameters_of_largeBasePartEmbedding
    A Target D fineAllowed hTarget b.1
    (hFamilyParts b.1 b.2)

end StructuralRamsey.Girth
