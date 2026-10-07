import Girth.ForestTreeRewire
import Girth.ForestReindex

/-! # Deleting finitely many one-edge members from a forest

An arbitrary subfamily of a forest of copies need not remain a forest.
Deleting a one-edge member is an exception, proved by join-tree rewiring.
This module iterates that operation across any finite family of one-edge
members, exactly as needed when removing auxiliary A-edges after the
circulation forest-completion gluing step.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Reindex the family remaining after inserting a deleted label as the
single-label erasure of the family remaining before that insertion. -/
def remainingAfterInsertEquiv
    [DecidableEq ι]
    (a : ι) (S : Finset ι) (ha : a ∉ S) :
    {i : ι // i ∉ insert a S} ≃
      {j : {i : ι // i ∉ S} //
        j ∈ (({(⟨a, ha⟩ : {i : ι // i ∉ S})} :
          Set {i : ι // i ∉ S})ᶜ)} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    have hiS : i.1 ∉ S := by
      intro hi
      exact i.2 (Finset.mem_insert_of_mem hi)
    let j : {i : ι // i ∉ S} := ⟨i.1, hiS⟩
    refine ⟨j, ?_⟩
    change j ≠ (⟨a, ha⟩ : {i : ι // i ∉ S})
    intro h
    have hval : i.1 = a := congrArg Subtype.val h
    exact i.2 (by simp [hval])
  · intro j
    have hjNe : j.1.1 ≠ a := by
      intro hval
      have hsub : j.1 = (⟨a, ha⟩ : {i : ι // i ∉ S}) :=
        Subtype.ext hval
      have hnot :
          j.1 ≠ (⟨a, ha⟩ : {i : ι // i ∉ S}) := by
        simpa using j.2
      exact hnot hsub
    refine ⟨j.1.1, ?_⟩
    intro hmem
    rcases Finset.mem_insert.mp hmem with hEq | hS
    · exact hjNe hEq
    · exact j.1.2 hS
  · intro i
    apply Subtype.ext
    rfl
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Deleting any finite collection of one-edge members preserves the forest
condition, even though deleting arbitrary members need not. -/
theorem ForestOfCopies.erase_finite_oneEdges
    [Fintype ι]
    {F : ι → HypergraphPiece W}
    (hForest : ForestOfCopies F)
    (S : Finset ι)
    (hOne : ∀ i : ι, i ∈ S → (F i).IsOneEdge) :
    ForestOfCopies
      (fun i : {i : ι // i ∉ S} => F i.1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      let e : {i : ι // i ∉ (∅ : Finset ι)} ≃ ι :=
        { toFun := fun i => i.1
          invFun := fun i => ⟨i, by simp⟩
          left_inv := by
            intro i
            apply Subtype.ext
            rfl
          right_inv := by intro i; rfl }
      simpa [e] using hForest.reindex e
  | @insert a S ha ih =>
      have hOneS : ∀ i : ι, i ∈ S → (F i).IsOneEdge := by
        intro i hi
        exact hOne i (Finset.mem_insert_of_mem hi)
      have hRemaining :
          ForestOfCopies (fun i : {i : ι // i ∉ S} => F i.1) :=
        ih hOneS
      let aS : {i : ι // i ∉ S} := ⟨a, ha⟩
      letI : Nonempty {i : ι // i ∉ S} := ⟨aS⟩
      obtain ⟨J⟩ := hRemaining.joinTree_of_nonempty
      have haOne : (F a).IsOneEdge :=
        hOne a (Finset.mem_insert_self a S)
      have hErase :=
        ForestOfCopies.erase_oneEdge
          hRemaining J (center := aS) haOne
      let e := remainingAfterInsertEquiv a S ha
      simpa [e, remainingAfterInsertEquiv, erasePiece] using
        hErase.reindex e

end StructuralRamsey.Girth
