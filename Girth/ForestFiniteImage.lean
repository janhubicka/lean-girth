import Girth.ForestTreeRewire
import Girth.ForestReindex

/-! # Forests on the distinct image of a finite family -/

namespace StructuralRamsey.Girth

open scoped Classical

universe v
variable {W I : Type v}

/-- Delete finitely many members when each deleted carrier is contained in a
retained carrier. The retained member gives a hub for each join-tree deletion. -/
theorem ForestOfCopies.restrict_compl_of_contained
    {F : I → HypergraphPiece W} [Fintype I]
    (hForest : ForestOfCopies F) (removed : Finset I)
    (hContained : ∀ i ∈ removed, ∃ j ∉ removed, (F i).carrier ⊆ (F j).carrier) :
    ForestOfCopies (fun i : {i : I // i ∉ removed} => F i.1) := by
  classical
  induction removed using Finset.induction_on with
  | empty =>
      let e : {i : I // i ∉ (∅ : Finset I)} ≃ I :=
        { toFun := Subtype.val
          invFun := fun i => ⟨i, by simp⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => rfl }
      exact hForest.reindex e
  | @insert center removed hNew ih =>
      let Remaining := {i : I // i ∉ removed}
      let c : Remaining := ⟨center, hNew⟩
      letI : Nonempty Remaining := ⟨c⟩
      have hPrevious : ForestOfCopies (fun i : Remaining => F i.1) := by
        apply ih
        intro i hi
        obtain ⟨j, hj, hSub⟩ := hContained i (Finset.mem_insert_of_mem hi)
        exact ⟨j, fun h => hj (Finset.mem_insert_of_mem h), hSub⟩
      obtain ⟨j, hj, hSub⟩ := hContained center (Finset.mem_insert_self _ _)
      let hub : Remaining := ⟨j, fun h => hj (Finset.mem_insert_of_mem h)⟩
      have hHub : hub ≠ c := fun h => hj (by simp [show j = center from congrArg Subtype.val h])
      obtain ⟨J⟩ := hPrevious.joinTree_of_nonempty
      have hErased : ForestOfCopies (erasePiece (fun i : Remaining => F i.1) c) :=
        ⟨JoinTree.pairwiseAllowed_erase hPrevious.pairwiseAllowed c,
          Or.inr (J.nonempty_eraseMember_of_full hHub hSub)⟩
      let e : {i : I // i ∉ insert center removed} ≃
          {i : Remaining // i ∈ ({c} : Set Remaining)ᶜ} :=
        { toFun := fun i => ⟨⟨i.1, fun h => i.2 (Finset.mem_insert_of_mem h)⟩,
            fun h => i.2 (by simp [show i.1 = center from congrArg Subtype.val h])⟩
          invFun := fun i => ⟨i.1.1, fun h => (Finset.mem_insert.mp h).elim
            (fun hEq => i.2 (Set.mem_singleton_iff.mpr (Subtype.ext hEq))) i.1.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
      exact hErased.reindex e

/-- A labelled forest gives a forest on its distinct pieces. A repeated member
can be deleted because its chosen representative has the same carrier. -/
theorem ForestOfCopies.finiteImage
    [Fintype I] (F : I → HypergraphPiece W) (hForest : ForestOfCopies F) :
    ForestOfCopies (fun P : {P : HypergraphPiece W // P ∈ Finset.univ.image F} => P.1) := by
  classical
  let Pieces := {P : HypergraphPiece W // P ∈ Finset.univ.image F}
  letI : Fintype Pieces := Finset.fintypeCoeSort (Finset.univ.image F)
  let rep : Pieces → I := fun P => Classical.choose (Finset.mem_image.mp P.2)
  have hRep (P : Pieces) : F (rep P) = P.1 :=
    (Classical.choose_spec (Finset.mem_image.mp P.2)).2
  let kept : Finset I := Finset.univ.image rep
  let removed : Finset I := Finset.univ \ kept
  have hKept (P : Pieces) : rep P ∈ kept := Finset.mem_image.mpr ⟨P, Finset.mem_univ _, rfl⟩
  have hComplement : ∀ i, i ∉ removed ↔ i ∈ kept := by
    intro i
    simp [removed]
  have hRetained := hForest.restrict_compl_of_contained removed (by
    intro i _
    let P : Pieces := ⟨F i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    refine ⟨rep P, (hComplement _).mpr (hKept P), ?_⟩
    rw [hRep P])
  let label : Pieces → {i : I // i ∉ removed} :=
    fun P => ⟨rep P, (hComplement _).mpr (hKept P)⟩
  have hBij : Function.Bijective label := by
    constructor
    · intro P Q h
      apply Subtype.ext
      exact (hRep P).symm.trans ((congrArg (fun i => F i.1) h).trans (hRep Q))
    · intro i
      obtain ⟨P, _, h⟩ := Finset.mem_image.mp ((hComplement _).mp i.2)
      exact ⟨P, Subtype.ext h⟩
  have hResult := hRetained.reindex (Equiv.ofBijective label hBij)
  have hFamily : (fun P : Pieces => F ((Equiv.ofBijective label hBij) P).1) =
      (fun P : Pieces => P.1) := funext hRep
  rwa [hFamily] at hResult

end StructuralRamsey.Girth
