import Girth.ForestMarkedNeutralFamily
import Girth.ForestNeutralGap
import SuccessorTree.FreeAncestralGapShape

/-!
# Finite compatible neutral-gap schedules for marked B-history families

A neutral-gap schedule records each *simultaneous* one-gap insertion
on the full marked q-family, using one global choice function at
each step. Since all insertions are actual free ancestral shape maps,
a finite schedule composes to one shape map from the first family
to the last.

Together with the separate compatibility test for one gap, this
is the formal multi-gap synthesis part of the bounded-presentation
argument. The converse -- extracting such a schedule from every
geometrically relevant B-tuple under a bounded active diary guard --
remains an application-level task. No globally carrier-faithful
evaluation is claimed.
-/

namespace StructuralRamsey.Girth

open SuccessorTree
open SuccessorTree.FreeAncestral

universe u
variable {Label : Type u} {arity : ℕ}
variable [Fintype Label] [Nonempty Label]

/-- Finite successive global one-gap replays from one marked q-family.
Each inserted step uses the same code-choice function across *all*
q histories; no branch-dependent shape map is permitted. -/
inductive FiniteGapReplaySchedule
    (q start : ℕ)
    (initial : Fin q → History Label arity start) :
    (N : ℕ) → (Fin q → History Label arity N) → Prop where
  | identity :
      FiniteGapReplaySchedule q start initial start initial
  | insert {N : ℕ}
      {before : Fin q → History Label arity N}
      (hprev : FiniteGapReplaySchedule q start initial N before)
      (m : ℕ)
      (choose : History Label arity m → Code Label arity m)
      (after : Fin q → History Label arity (N + 1))
      (hstep :
        ∀ i : Fin q,
          gapNode m choose (⟨N, before i⟩ : Node Label arity) =
            (⟨N + 1, after i⟩ : Node Label arity)) :
      FiniteGapReplaySchedule q start initial (N + 1) after

/-- One global shape map realizes every step of a finite marked
neutral-gap schedule simultaneously. -/
theorem FiniteGapReplaySchedule.exists_shape
    (q start : ℕ)
    (initial : Fin q → History Label arity start) :
    ∀ {N : ℕ} {target : Fin q → History Label arity N},
      FiniteGapReplaySchedule
        (Label := Label) (arity := arity) q start initial N target →
      ∃ F : ShapeMap
          (freeSTree (Label := Label) (arity := arity)),
        ∀ i : Fin q,
          F (⟨start, initial i⟩ : Node Label arity) =
            (⟨N, target i⟩ : Node Label arity) := by
  intro N target h
  induction h with
  | identity =>
      refine ⟨ShapeMap.id
        (freeSTree (Label := Label) (arity := arity)), ?_⟩
      intro i
      rfl
  | @insert N before hprev m choose after hstep ih =>
      obtain ⟨F, hF⟩ := ih
      refine ⟨(oneGapShapeMap m choose).comp F, ?_⟩
      intro i
      change
        oneGapShapeMap m choose
          (F (⟨start, initial i⟩ : Node Label arity)) =
          (⟨N + 1, after i⟩ : Node Label arity)
      rw [hF i]
      change
        gapNode m choose (⟨N, before i⟩ : Node Label arity) =
          (⟨N + 1, after i⟩ : Node Label arity)
      exact hstep i

/-- A compatible one-gap family yields the corresponding one-step
schedule, not merely unrelated preimages for its members. -/
theorem finiteMarkedFamily_oneStepSchedule
    (m k q : ℕ)
    (P : Fin q →
      MarkedNeutralGap (Label := Label) (arity := arity) m k)
    (hConsistent :
      ∀ i j : Fin q, (P i).stem = (P j).stem →
        (P i).insertedCode = (P j).insertedCode) :
    ∃ initial : Fin q → History Label arity (m + k),
      FiniteGapReplaySchedule (Label := Label) (arity := arity)
        q (m + k) initial (m + k + 1)
          (fun i => (P i).history) := by
  obtain ⟨choose, initial, hMaps⟩ :=
    finiteMarkedNeutralGap_preimages m k q P hConsistent
  have hIdentity :
      FiniteGapReplaySchedule (Label := Label) (arity := arity)
        q (m + k) initial (m + k) initial := by
    exact .identity
  exact ⟨initial,
    FiniteGapReplaySchedule.insert
      hIdentity m choose (fun i => (P i).history) hMaps⟩

end StructuralRamsey.Girth
