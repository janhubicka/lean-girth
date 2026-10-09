import Girth.ForestCompletionProperty
import Girth.CompletionBudget
import Mathlib.Tactic

/-!
# Used standard-copy owners and the empty selected family

The circulation completion induction chooses one standard-picture owner for
each selected A- or B-piece. The finite owner family should consist precisely
of those owners actually used, not an arbitrary larger list of standard
pictures. This makes the owner map surjective by construction and ensures
that its cardinality does not exceed the number of selected pieces.

The empty selected family needs no standard owner or local connector: its
empty forest is itself an admissible completion. Thus the nonempty-owner
assumption in the existing local completion theorem loses no generality.

This module is independent of the local-forest partite lemma. It closes only
the finite owner indexing and empty-family bookkeeping steps of certpres.
-/

namespace StructuralRamsey.Girth

universe v
variable {N Q W : Type v}

/-- Index only the standard-picture owners used by some selected piece. -/
abbrev UsedOwner (owner : N → Q) : Type v :=
  {q : Q // q ∈ Set.range owner}

/-- The chosen owner of a selected piece, now viewed as a used owner. -/
def usedOwnerMap (owner : N → Q) (n : N) : UsedOwner owner :=
  ⟨owner n, ⟨n, rfl⟩⟩

@[simp] theorem usedOwnerMap_val (owner : N → Q) (n : N) :
    (usedOwnerMap owner n).1 = owner n := rfl

/-- No unused standard-picture index remains: every used owner is
the owner of an actual selected piece. -/
theorem usedOwnerMap_surjective (owner : N → Q) :
    Function.Surjective (usedOwnerMap owner) := by
  rintro ⟨q, ⟨n, hn⟩⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  exact hn

/-- A finite selected family has finitely many distinct owners, even
if the ambient family of all standard pictures is infinite. -/
theorem usedOwner_finite [Finite N] (owner : N → Q) :
    Finite (UsedOwner owner) :=
  Finite.of_surjective (usedOwnerMap owner) (usedOwnerMap_surjective owner)

/-- The canonical finite type of actually used standard-picture owners. -/
noncomputable def usedOwnerFintype [Fintype N] (owner : N → Q) :
    Fintype (UsedOwner owner) := by
  letI : Finite (UsedOwner owner) := usedOwner_finite owner
  exact Fintype.ofFinite _

/-- The number of distinct standard-picture owners cannot exceed the
number of selected A/B-pieces; this is a consequence of the canonical
surjective owner map and needs no chosen section. -/
theorem usedOwner_card_le [Fintype N]
    (owner : N → Q) :
    letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
    Fintype.card (UsedOwner owner) ≤ Fintype.card N := by
  classical
  letI : Fintype (UsedOwner owner) := usedOwnerFintype owner
  exact Fintype.card_le_of_surjective
    (usedOwnerMap owner) (usedOwnerMap_surjective owner)

/-- If at least one selected piece exists, so does at least one used
owner. The global completion proof may therefore split off the empty
family and invoke its local join-tree assembly on the used owners. -/
theorem usedOwner_nonempty [Nonempty N] (owner : N → Q) :
    Nonempty (UsedOwner owner) :=
  ⟨usedOwnerMap owner (Classical.choice inferInstance)⟩

/-- There is no auxiliary member to add when the selected family is
empty; the empty family satisfies the exact designated-completion
predicate, including its classification condition. -/
theorem emptySelected_forestCompletionWitness
    [IsEmpty N]
    (selected : N → HypergraphPiece W)
    (designated : HypergraphPiece W → Prop) :
    ForestCompletionWitness selected designated
      (fun k : PEmpty.{v+1} => isEmptyElim k) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, Or.inl inferInstance⟩
    intro i
    exact isEmptyElim i
  · intro n
    exact isEmptyElim n
  · intro k
    exact isEmptyElim k

/-- Empty selections satisfy the existential forest-completion conclusion
without using the old induction hypothesis or constructing any owner. -/
theorem emptySelected_hasForestCompletion
    [IsEmpty N]
    (selected : N → HypergraphPiece W)
    (designated : HypergraphPiece W → Prop) :
    ∃ (K : Type v), ∃ (_ : Fintype K),
      ∃ completed : K → HypergraphPiece W,
        ForestCompletionWitness selected designated completed := by
  refine ⟨PEmpty.{v+1}, inferInstance, ?_⟩
  exact ⟨(fun k : PEmpty.{v+1} => isEmptyElim k),
    emptySelected_forestCompletionWitness selected designated⟩

end StructuralRamsey.Girth
