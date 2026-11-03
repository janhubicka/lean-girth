import Girth.TrainRecursiveActivePartite
import PartiteConstruction.Partite.Induced

set_option autoImplicit false

/-!
# A genuine large partite Ramsey base with part-preserving selected labels

The large-base repair of Track D requires more than an abstract choice
of a base big enough to contain the full active target. We can build
such a base by the checked induced partite Hales--Jewett power of the
true active target, over its ORIGINAL A-coordinate parts.

The result packages all the usable facts simultaneously:
* the power base is finite and partite over A;
* the complete family of its PARTITE embeddings of the target is
  nonempty for a nonempty finite colour type;
* every prescribed relational base embedding in that family preserves
  the A-part map exactly;
* the family itself satisfies the induced partite Ramsey arrow.

The vertex carrier of the base is the full power type (larger than
the A-vertex set), so #768 does not obstruct its target embeddings.
No edge/wagon is pruned and no distinct selected labels are merged.

This is not yet a complete forest witness or fine-train construction.
In particular, system-girth, mixed forest, train restriction and
the attached-output supreme-cycle transfer must be established by the
lower recursive assertion and the actual partite picture step.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {Q VB : Type v}

/-- Use the induced partite Hales--Jewett theorem to choose a LARGE
base whose selected relational target copies have the genuine coarse
part-map compatibility required in Track D.  The family consists of
all true partite embeddings; there is no total-order or rigidity
assumption on arbitrary relational embeddings. -/
theorem exists_largeBase_partiteRamseyFamily
    (A : RelStructure L Q)
    (B : StructuralRamsey.Partite.System L Q VB)
    [Finite Q] [Finite VB]
    (hB : B.IsPartiteOver A)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (N : ℕ), 0 < N ∧
      let D := StructuralRamsey.Partite.Induced.power B N
      D.IsPartiteOver A ∧
      ∃ family : Set (Embedding B.toRelStructure D.toRelStructure),
        Nonempty family ∧
        (∀ b, b ∈ family → ∀ x : VB,
          D.part (b x) = B.part x) ∧
        (∀ χ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A) D → κ,
          ∃ b : StructuralRamsey.Partite.Embedding B D,
            b.toEmbedding ∈ family ∧
            ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
                (StructuralRamsey.Partite.transversal A) B,
              χ (b.comp a₁) = χ (b.comp a₂)) := by
  classical
  obtain ⟨N, hN, hArrow⟩ :=
    StructuralRamsey.Partite.Induced.partiteLemma
      (A := A) (B := B) hB κ
  refine ⟨N, hN, ?_⟩
  let D := StructuralRamsey.Partite.Induced.power B N
  have hD : D.IsPartiteOver A :=
    StructuralRamsey.Partite.Induced.power_isPartiteOver hB hN
  let family : Set (Embedding B.toRelStructure D.toRelStructure) :=
    Set.range (fun b : StructuralRamsey.Partite.Embedding B D =>
      b.toEmbedding)
  refine ⟨hD, family, ?_, ?_, ?_⟩
  · let colour : κ := Classical.choice (inferInstance : Nonempty κ)
    obtain ⟨b, _⟩ := hArrow (fun _ => colour)
    exact ⟨b.toEmbedding, ⟨b, rfl⟩⟩
  · intro b hb x
    rcases hb with ⟨g, rfl⟩
    exact g.map_part x
  · intro χ
    obtain ⟨b, hMono⟩ := hArrow χ
    exact ⟨b, ⟨b, rfl⟩, hMono⟩

end StructuralRamsey.Girth
