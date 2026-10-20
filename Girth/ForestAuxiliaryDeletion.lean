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


/-- A temporary singleton separator can be removed from a forest, even if
its unique vertex is isolated in every genuine support piece.

The proof regards the singleton as a *formal* one-edge piece on its own
carrier, uses the already verified one-edge deletion theorem, and then
forgets the formal edge. The formal edge is not an ambient hyperedge, and
no uniformity assertion is made about the intermediate family. -/
theorem ForestOfCopies.erase_subsingletonCarrier
    {F : ι → HypergraphPiece W} [Fintype ι]
    (hF : ForestOfCopies F)
    (J : JoinTree F)
    {center : ι}
    (hSmall : (F center).carrier.Subsingleton) :
    ForestOfCopies (erasePiece F center) := by
  classical
  let G : ι → HypergraphPiece W := fun i =>
    if h : i = center then
      { carrier := (F i).carrier
        edges := {(F i).carrier}
        edge_subset_carrier := by
          intro e he
          have heq : e = (F i).carrier := Set.mem_singleton_iff.mp he
          simpa [heq] }
    else F i
  have hCarrier (i : ι) :
      (G i).carrier = (F i).carrier := by
    by_cases hi : i = center <;> simp [G, hi]
  have hOne : (G center).IsOneEdge := by
    simp [G, HypergraphPiece.IsOneEdge]
  have hPair : PairwiseAllowed G := by
    intro i j hij
    by_cases hi : i = center
    · left
      intro x hx y hy
      apply hSmall
      · simpa [hCarrier i, hi] using hx.1
      · simpa [hCarrier i, hi] using hy.1
    · by_cases hj : j = center
      · left
        intro x hx y hy
        apply hSmall
        · simpa [hCarrier j, hj] using hx.2
        · simpa [hCarrier j, hj] using hy.2
      · simpa [G, hi, hj] using hF.pairwiseAllowed hij
  let JG : JoinTree G :=
    { tree := J.tree
      isTree := J.isTree
      running := by
        intro x
        have hOcc :
            {i : ι | x ∈ (G i).carrier} =
            {i : ι | x ∈ (F i).carrier} := by
          ext i
          simp only [Set.mem_setOf_eq, hCarrier i]
        simpa only [hOcc] using J.running x }
  have hG : ForestOfCopies G := ⟨hPair, Or.inr ⟨JG⟩⟩
  have hErased := hG.erase_oneEdge JG hOne
  have hAgree : erasePiece G center = erasePiece F center := by
    funext z
    have hz : z.1 ≠ center := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
    simp [erasePiece, G, hz]
  rw [hAgree] at hErased
  exact hErased

end StructuralRamsey.Girth
