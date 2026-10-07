import Girth.ForestTreeRewire
import Girth.ForestReindex

/-! # Deleting all auxiliary one-edge members

The circulation forest-completion argument first glues local forests,
including temporary one-A-edge connectors, and then removes those connectors.
The single-edge deletion theorem extends by finite induction to any prescribed
family of auxiliary one-edge members.  This is not arbitrary subfamily
heredity: the restriction is only justified when every removed member has
exactly one edge.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Removing any finite set of one-edge members from a finite forest preserves
the forest property.  The surviving labels are those outside `removed`. -/
theorem ForestOfCopies.restrict_compl_of_oneEdge
    {F : ι → HypergraphPiece W} [Fintype ι]
    (hF : ForestOfCopies F)
    (removed : Finset ι)
    (hOne : ∀ i : ι, i ∈ removed → (F i).IsOneEdge) :
    ForestOfCopies
      (fun i : {i : ι // i ∉ removed} => F i.1) := by
  classical
  induction removed using Finset.induction_on with
  | empty =>
      let e : {i : ι // i ∉ (∅ : Finset ι)} ≃ ι :=
        { toFun := Subtype.val
          invFun := fun i => ⟨i, by simp⟩
          left_inv := by
            intro i
            exact Subtype.ext rfl
          right_inv := by intro i; rfl }
      simpa [e] using hF.reindex e
  | @insert center removed hnot ih =>
      have hOneRest :
          ∀ i : ι, i ∈ removed → (F i).IsOneEdge := by
        intro i hi
        exact hOne i (Finset.mem_insert_of_mem hi)
      have hPrev :
          ForestOfCopies
            (fun i : {i : ι // i ∉ removed} => F i.1) :=
        ih hOneRest
      let oldI := {i : ι // i ∉ removed}
      let c : oldI := ⟨center, hnot⟩
      letI : Nonempty oldI := ⟨c⟩
      let J : JoinTree
          (fun i : oldI => F i.1) :=
        Classical.choice hPrev.joinTree_of_nonempty
      have hc : (F c.1).IsOneEdge := by
        exact hOne center (Finset.mem_insert_self _ _)
      have hErased :
          ForestOfCopies
            (erasePiece (fun i : oldI => F i.1) c) :=
        hPrev.erase_oneEdge J hc
      let surviving := {i : ι // i ∉ insert center removed}
      let erased := {i : oldI // i ∈ (({c} : Set oldI)ᶜ)}
      let e : surviving ≃ erased :=
        { toFun := fun i =>
            ⟨⟨i.1, by
                intro hi
                exact i.2 (Finset.mem_insert_of_mem hi)⟩,
              by
                change
                  (⟨i.1, by
                    intro hi
                    exact i.2 (Finset.mem_insert_of_mem hi)⟩ : oldI) ≠ c
                intro h
                have hv : i.1 = center := congrArg Subtype.val h
                exact i.2 (by simp [hv])⟩
          invFun := fun i =>
            ⟨i.1.1, by
              have hne : i.1 ≠ c := by
                simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
                  using i.2
              have hval : i.1.1 ≠ center := by
                intro hv
                apply hne
                apply Subtype.ext
                exact hv
              intro hmem
              rcases Finset.mem_insert.mp hmem with heq | hrest
              · exact hval heq
              · exact i.1.2 hrest⟩
          left_inv := by
            intro i
            exact Subtype.ext rfl
          right_inv := by
            intro i
            apply Subtype.ext
            apply Subtype.ext
            rfl }
      change ForestOfCopies (fun i : surviving => F i.1)
      exact hErased.reindex e

/-- Keep any chosen family of members, provided every member not kept is a
one-edge auxiliary member.  This is the form used when gluing the local
completion forests and discarding their temporary connectors. -/
theorem ForestOfCopies.restrict_of_oneEdge_outside
    {F : ι → HypergraphPiece W} [Fintype ι]
    (hF : ForestOfCopies F)
    (keep : Finset ι)
    (hOne : ∀ i : ι, i ∉ keep → (F i).IsOneEdge) :
    ForestOfCopies
      (fun i : {i : ι // i ∈ keep} => F i.1) := by
  classical
  let removed : Finset ι := Finset.univ \ keep
  have hRemoved :
      ∀ i : ι, i ∈ removed → (F i).IsOneEdge := by
    intro i hi
    apply hOne i
    simpa [removed] using hi
  have hBase :=
    hF.restrict_compl_of_oneEdge removed hRemoved
  let e :
      {i : ι // i ∈ keep} ≃ {i : ι // i ∉ removed} :=
    { toFun := fun i =>
        ⟨i.1, by
          simpa [removed] using i.2⟩
      invFun := fun i =>
        ⟨i.1, by
          simpa [removed] using i.2⟩
      left_inv := by
        intro i
        exact Subtype.ext rfl
      right_inv := by
        intro i
        exact Subtype.ext rfl }
  exact hBase.reindex e

end StructuralRamsey.Girth
