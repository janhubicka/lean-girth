import Girth.ForestJoinGlue

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
    JoinTree (fun _ : PUnit => F) := by
  classical
  refine
    { tree := SimpleGraph.starGraph PUnit.unit
      isTree := SimpleGraph.isTree_starGraph PUnit.unit
      running := ?_ }
  intro x
  by_cases hx : x ∈ F.carrier
  · have hcenter :
        PUnit.unit ∈
          {i : PUnit | x ∈ ((fun _ : PUnit => F) i).carrier} := by
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
    PairwiseAllowed (fun _ : PUnit => F) := by
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
    ForestOfCopies (sumPieces Y (fun _ : PUnit => F)) := by
  classical
  let JY : JoinTree Y :=
    Classical.choice hY.joinTree_of_nonempty
  let JF : JoinTree (fun _ : PUnit => F) :=
    joinTree_singlePiece F
  have hCrossOcc :
      ∀ (x : W) (i : ι) (j : PUnit),
        x ∈ (Y i).carrier →
        x ∈ F.carrier →
          x ∈ (Y p).carrier ∧ x ∈ F.carrier := by
    intro x i j hxi hxF
    have hxDom :
        x ∈ F.carrier ∩ (Y p).carrier :=
      hDom i ⟨hxF, hxi⟩
    exact ⟨hxDom.2, hxDom.1⟩
  have hCrossAllowed' :
      ∀ (i : ι) (j : PUnit),
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
    ForestOfCopies (sumPieces Y (fun _ : PUnit => F)) := by
  classical
  let p : ι := Classical.choice (inferInstance : Nonempty ι)
  apply forestOfCopies_attach_dominated hY F hCrossAllowed p
  intro i x hx
  exfalso
  exact Set.disjoint_left.mp (hDisj i) hx.1 hx.2

end StructuralRamsey.Girth
