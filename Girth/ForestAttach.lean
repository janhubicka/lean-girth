import Girth.ForestJoinGlue
import Mathlib.Data.Fintype.Lattice

/-! # Attaching one dominated leaf to a forest

This is the finite join-tree lemma used by the successor-profile proof.
If all intersections of a new piece with an old forest are contained in one
old intersection, the new piece can be attached as one leaf.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- The one-piece family has the tautological join tree. -/
noncomputable def joinTree_singlePiece
    (F : HypergraphPiece W) :
    JoinTree (fun _ : PUnit.{v+1} => F) := by
  classical
  refine
    { tree := SimpleGraph.starGraph PUnit.unit
      isTree := SimpleGraph.isTree_starGraph PUnit.unit
      running := ?_ }
  intro x
  by_cases hx : x ∈ F.carrier
  · have hcenter :
        PUnit.unit ∈
          {i : PUnit.{v+1} | x ∈ ((fun _ : PUnit.{v+1} => F) i).carrier} := by
      simpa using hx
    exact
      starGraph_induce_preconnected_of_mem_center
        PUnit.unit hcenter
  · intro a b
    exfalso
    apply hx
    exact a.2

/-- Pairwise allowed intersections are automatic in a one-piece family. -/
theorem pairwiseAllowed_singlePiece
    (F : HypergraphPiece W) :
    PairwiseAllowed (fun _ : PUnit.{v+1} => F) := by
  intro i j hij
  exfalso
  exact hij (Subsingleton.elim i j)

/-- Attach a new piece to an old forest when one old member dominates all
intersections of the new piece with the old family.

The conclusion is indexed by the sum of the old labels with one new label. -/
theorem forestOfCopies_attach_dominated
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection (Y i) F)
    (p : ι)
    (hDom :
      ∀ i : ι,
        F.carrier ∩ (Y i).carrier ⊆
          F.carrier ∩ (Y p).carrier) :
    ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F)) := by
  classical
  let JY : JoinTree Y :=
    Classical.choice hY.joinTree_of_nonempty
  let JF : JoinTree (fun _ : PUnit.{v+1} => F) :=
    joinTree_singlePiece F
  have hCrossOcc :
      ∀ (x : W) (i : ι) (j : PUnit.{v+1}),
        x ∈ (Y i).carrier →
        x ∈ F.carrier →
          x ∈ (Y p).carrier ∧ x ∈ F.carrier := by
    intro x i j hxi hxF
    have hxDom :
        x ∈ F.carrier ∩ (Y p).carrier :=
      hDom i ⟨hxF, hxi⟩
    exact ⟨hxDom.2, hxDom.1⟩
  have hCrossAllowed' :
      ∀ (i : ι) (j : PUnit.{v+1}),
        AllowedIntersection (Y i) F := by
    intro i j
    exact hCrossAllowed i
  exact
    forestOfCopies_sumBridge
      JY JF
      hY.pairwiseAllowed
      (pairwiseAllowed_singlePiece F)
      p PUnit.unit
      hCrossOcc hCrossAllowed'

/-- A disjoint new piece is a special case of dominated attachment. -/
theorem forestOfCopies_attach_disjoint
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection (Y i) F)
    (hDisj :
      ∀ i : ι, Disjoint F.carrier (Y i).carrier) :
    ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F)) := by
  classical
  let p : ι := Classical.choice (inferInstance : Nonempty ι)
  apply forestOfCopies_attach_dominated hY F hCrossAllowed p
  intro i x hx
  exfalso
  exact Set.disjoint_left.mp (hDisj i) hx.1 hx.2


/-- Contrapositive form used by the successor-profile proof: if adding the new
piece to the old forest fails to be a forest, then no old member dominates all
intersections of the new piece with the old family. -/
theorem no_dominating_member_of_not_forest
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection (Y i) F)
    (hBad :
      ¬ ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F))) :
    ∀ p : ι, ∃ i : ι,
      ¬(F.carrier ∩ (Y i).carrier ⊆
        F.carrier ∩ (Y p).carrier) := by
  intro p
  by_contra h
  have hDom :
      ∀ i : ι,
        F.carrier ∩ (Y i).carrier ⊆
          F.carrier ∩ (Y p).carrier := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  exact hBad
    (forestOfCopies_attach_dominated
      hY F hCrossAllowed p hDom)


/-- A finite family of boundary intersections which is totally ordered by
inclusion has a dominating member. Finiteness of the ambient vertex set
is unnecessary: we maximize by scanning the finite family of labels. -/
theorem exists_dominating_member_of_comparable
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (F : HypergraphPiece W)
    (hComp :
      ∀ i j : ι,
        F.carrier ∩ (Y i).carrier ⊆
            F.carrier ∩ (Y j).carrier ∨
        F.carrier ∩ (Y j).carrier ⊆
            F.carrier ∩ (Y i).carrier) :
    ∃ p : ι, ∀ i : ι,
      F.carrier ∩ (Y i).carrier ⊆
        F.carrier ∩ (Y p).carrier := by
  classical
  let root : ι := Classical.choice (inferInstance : Nonempty ι)
  have hFin (s : Finset ι) :
      ∃ p : ι, ∀ i : ι, i ∈ s →
        F.carrier ∩ (Y i).carrier ⊆
          F.carrier ∩ (Y p).carrier := by
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨root, ?_⟩
        intro i hi
        simp at hi
    | @insert j s hjs ih =>
        obtain ⟨p, hp⟩ := ih
        rcases hComp j p with hjp | hpj
        · refine ⟨p, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hjp
          · exact hp i his
        · refine ⟨j, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact Set.Subset.rfl
          · exact (hp i his).trans hpj
  obtain ⟨p, hp⟩ := hFin Finset.univ
  exact ⟨p, fun i => hp i (Finset.mem_univ i)⟩

/-- Exact finite form used in the successor-profile proof: if attaching a new
piece to a forest is bad, then two of its old boundary intersections are
incomparable. -/
theorem exists_incomparable_intersections_of_not_forest
    [Fintype ι] [Nonempty ι]
    {Y : ι → HypergraphPiece W}
    (hY : ForestOfCopies Y)
    (F : HypergraphPiece W)
    (hCrossAllowed :
      ∀ i : ι, AllowedIntersection (Y i) F)
    (hBad :
      ¬ ForestOfCopies (sumPieces Y (fun _ : PUnit.{v+1} => F))) :
    ∃ i j : ι,
      ¬(F.carrier ∩ (Y i).carrier ⊆
        F.carrier ∩ (Y j).carrier) ∧
      ¬(F.carrier ∩ (Y j).carrier ⊆
        F.carrier ∩ (Y i).carrier) := by
  classical
  by_contra hNo
  have hComp :
      ∀ i j : ι,
        F.carrier ∩ (Y i).carrier ⊆
            F.carrier ∩ (Y j).carrier ∨
        F.carrier ∩ (Y j).carrier ⊆
            F.carrier ∩ (Y i).carrier := by
    intro i j
    by_cases hij :
        F.carrier ∩ (Y i).carrier ⊆
          F.carrier ∩ (Y j).carrier
    · exact Or.inl hij
    · by_cases hji :
          F.carrier ∩ (Y j).carrier ⊆
            F.carrier ∩ (Y i).carrier
      · exact Or.inr hji
      · exfalso
        exact hNo ⟨i, j, hij, hji⟩
  obtain ⟨p, hp⟩ :=
    exists_dominating_member_of_comparable F hComp
  obtain ⟨i, hi⟩ :=
    no_dominating_member_of_not_forest
      hY F hCrossAllowed hBad p
  exact hi (hp i)

end StructuralRamsey.Girth
