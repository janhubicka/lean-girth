import Girth.TrainRecursiveWitnessPass
import Girth.ActivePicture
import PartiteConstruction.Partite.Induced

/-!
# Realizing finite-pass profiles as actual base embeddings

The finite pass enumerates injective maps from A's vertices to the parts.
The actual attachment increment is indexed by relational embeddings of A
into the base. An inhabited projected fibre supplies exactly such an
embedding: the partite projection is an embedding on an irreducible A-copy.

An empty fibre uses the identity transition, retaining every selected copy,
ambient edge and train level. Removing its profile from a readiness list is
a separate, explicit hypothesis. The reduction below only changes the
indexing of an already supplied actual local step; it asserts no local
Ramsey existence or automatic preservation of readiness.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA VB P X : Type v}

/-- The projection of an actual irreducible A-copy is an embedding into
the base with precisely the prescribed injective profile. -/
theorem baseEmbedding_of_projectedEmbedding
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible) (hPartite : C.IsPartiteOver D)
    (α : UA ↪ P) (a : StructuralRamsey.Partite.ProjectedEmbedding A C α) :
    ∃ e : Embedding A D, e.toFunctionEmbedding = α := by
  obtain ⟨e, he⟩ := hPartite.after_irreducible_embedding hA a.val
  refine ⟨e, ?_⟩
  apply Function.Embedding.ext
  intro x
  exact (he x).trans (a.property x)

/-- No choice of a new base profile is needed for a nonempty fibre. -/
theorem baseEmbedding_of_nonempty_projectedFibre
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible) (hPartite : C.IsPartiteOver D)
    (α : UA ↪ P)
    (hFibre : Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A C α)) :
    ∃ e : Embedding A D, e.toFunctionEmbedding = α := by
  obtain ⟨a⟩ := hFibre
  exact baseEmbedding_of_projectedEmbedding A D C hA hPartite α a

/-- A nonempty true active subsystem gives the exact embedding and active
nonemptiness expected by the concrete forest increment. -/
theorem baseEmbedding_of_nonempty_activeCarrier
    (A : RelStructure L UA) (D : RelStructure L P)
    (C : StructuralRamsey.Partite.System L P X)
    (hA : A.Irreducible) (hPartite : C.IsPartiteOver D)
    (α : UA ↪ P) (hActive : (activeCarrier A C α).Nonempty) :
    ∃ e : Embedding A D, e.toFunctionEmbedding = α ∧
      (activeCarrier A C e.toFunctionEmbedding).Nonempty := by
  obtain ⟨x, a, hx⟩ := hActive
  obtain ⟨e, he⟩ := baseEmbedding_of_projectedEmbedding A D C hA hPartite α a
  refine ⟨e, he, ?_⟩
  rw [he]
  exact ⟨x, a, hx⟩

/-- For nonempty A, fibre inhabitation and nonemptiness of the true active
vertex set agree. The source-nonemptiness hypothesis is necessary here. -/
theorem activeCarrier_nonempty_iff_projectedFibre [Nonempty UA]
    (A : RelStructure L UA) (C : StructuralRamsey.Partite.System L P X)
    (α : UA ↪ P) :
    (activeCarrier A C α).Nonempty ↔
      Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A C α) := by
  constructor
  · rintro ⟨x, a, hx⟩
    exact ⟨a⟩
  · rintro ⟨a⟩
    obtain ⟨u⟩ := ‹Nonempty UA›
    exact ⟨a.val u, a, u, rfl⟩

section Pass

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P} {family : Set (Embedding B D)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}

/-- An absent projected fibre is homogeneous under the identity transition.
No source ordering, finiteness or nonempty colour type is required. -/
theorem pictureStep_self_of_empty_projectedFibre
    (S : ForestTailStage A B D family t targetTrain allowed)
    (α : UA ↪ P) (κ : Type w)
    (hEmpty : ¬ Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system α)) :
    PictureStep S S α κ := by
  intro χ
  refine ⟨TransitionEmbedding.id S, ?_⟩
  intro a b
  exact (hEmpty ⟨a⟩).elim

/-- A profile that cannot be realized by an embedding into the base is
absent from every stage whose projection is a homomorphism-embedding. -/
theorem pictureStep_self_of_no_baseEmbedding
    (S : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (α : UA ↪ P) (κ : Type w)
    (hBase : ¬ ∃ e : Embedding A D, e.toFunctionEmbedding = α) :
    PictureStep S S α κ := by
  apply pictureStep_self_of_empty_projectedFibre S α κ
  intro hFibre
  exact hBase
    (baseEmbedding_of_nonempty_projectedFibre A D S.system hA S.isPartite α hFibre)

/-- Reduce one arbitrary-profile pass obligation to its concrete actual
base-embedding step. Empty-fibre readiness is explicitly supplied; it is
not inferred from the identity embedding or from the stage invariant. -/
theorem ForestTailStage.profileStep_of_actualStep
    (S : ForestTailStage A B D family t targetTrain allowed)
    (hA : A.Irreducible) (α : UA ↪ P) (remaining : List (UA ↪ P))
    (κ : Type w)
    (Ready : List (UA ↪ P) →
      ForestTailStage A B D family t targetTrain allowed → Prop)
    (hReady : Ready (α :: remaining) S)
    (hEmptyReady :
      ¬ Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system α) →
        Ready remaining S)
    (actualStep : ∀ e : Embedding A D,
      Nonempty (StructuralRamsey.Partite.ProjectedEmbedding A S.system
        e.toFunctionEmbedding) →
      Ready (e.toFunctionEmbedding :: remaining) S →
        ∃ T : ForestTailStage A B D family t targetTrain allowed,
          Ready remaining T ∧ PictureStep S T e.toFunctionEmbedding κ) :
    ∃ T : ForestTailStage A B D family t targetTrain allowed,
      Ready remaining T ∧ PictureStep S T α κ := by
  classical
  by_cases hFibre : Nonempty
      (StructuralRamsey.Partite.ProjectedEmbedding A S.system α)
  · obtain ⟨e, he⟩ := baseEmbedding_of_nonempty_projectedFibre
      A D S.system hA S.isPartite α hFibre
    have hFibreE : Nonempty
        (StructuralRamsey.Partite.ProjectedEmbedding A S.system e.toFunctionEmbedding) := by
      simpa only [he] using hFibre
    have hReadyE : Ready (e.toFunctionEmbedding :: remaining) S := by
      simpa only [he] using hReady
    obtain ⟨T, hReadyT, hStep⟩ := actualStep e hFibreE hReadyE
    exact ⟨T, hReadyT, by simpa only [he] using hStep⟩
  · exact ⟨S, hEmptyReady hFibre, pictureStep_self_of_empty_projectedFibre S α κ hFibre⟩

end Pass

/-- A finite list of every injective projection profile, without repetitions.
This enumerates all profiles, including those with an empty fibre. -/
noncomputable def projectionProfileList (UA P : Type v) [Finite UA] [Finite P] :
    List (UA ↪ P) := by
  classical
  letI : Fintype (UA ↪ P) := Fintype.ofFinite _
  exact (Finset.univ : Finset (UA ↪ P)).toList

theorem mem_projectionProfileList [Finite UA] [Finite P] (α : UA ↪ P) :
    α ∈ projectionProfileList UA P := by
  classical
  simp [projectionProfileList]

theorem projectionProfileList_nodup [Finite UA] [Finite P] :
    (projectionProfileList UA P).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- The prescribed base-family Ramsey arrow supplies the nonempty family
needed for the disjoint initial picture. It implies no vertex or support
nonemptiness beyond this literal family nonemptiness. -/
theorem baseFamily_nonempty_of_arrow
    (A : RelStructure L UA) (B : RelStructure L VB) (D : RelStructure L P)
    (family : Set (Embedding B D)) (κ : Type w) [Nonempty κ]
    (hBase : ∀ χ : Embedding A D → κ,
      ∃ b : Embedding B D, b ∈ family ∧
        ∀ a₁ a₂ : Embedding A B, χ (b.comp a₁) = χ (b.comp a₂)) :
    family.Nonempty := by
  obtain ⟨colour⟩ := ‹Nonempty κ›
  obtain ⟨b, hb, _⟩ := hBase (fun _ => colour)
  exact ⟨b, hb⟩

end StructuralRamsey.Girth.TrainRecursiveWitness
