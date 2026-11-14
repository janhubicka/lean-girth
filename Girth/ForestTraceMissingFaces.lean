import Girth.ForestJoinTreeHelly
import Girth.ForestTraceRestriction

/-!
# The missing-face version of join-tree Helly

If every vertex-deletion face of a nonempty set K is contained in
an original bag of the same join-tree family, and every two vertices
of K can be avoided by some third vertex of K, then one ORIGINAL
bag contains all of K.  In the manuscript this applies to a
minimal uncovered clique K of size at least three.

The proof does not require any chordal or clique-tree theorem.  It
also never constructs a new bag: the conclusion is a member of
the original indexed family.  The finite bound on the number of
chosen missing faces is handled separately in local completion.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- The precise missing-face form of the join-tree Helly argument. -/
theorem JoinTree.missingFaces_contained_in_one_bag
    {F : ι → HypergraphPiece W} [Fintype ι] [Nonempty ι]
    (J : JoinTree F)
    {K : Set W} (hK : K.Nonempty)
    (hThird : ∀ x : W, x ∈ K →
      ∀ y : W, y ∈ K →
        ∃ z : W, z ∈ K ∧ z ≠ x ∧ z ≠ y)
    (faceBag : W → ι)
    (hFace : ∀ z : W, z ∈ K →
      ∀ x : W, x ∈ K → x ≠ z →
        x ∈ (F (faceBag z)).carrier) :
    ∃ i : ι, K ⊆ (F i).carrier := by
  apply J.pairCovered_in_one_bag hK
  intro x hx y hy
  obtain ⟨z, hz, hzx, hzy⟩ := hThird x hx y hy
  exact ⟨faceBag z,
    hFace z hz x hx hzx.symm,
    hFace z hz y hy hzy.symm⟩

/-- Applied to a join-tree completion indexed by a FINITE set of
actual original cover members.  Selected missing-face indices must
occur inside this completion; the resulting containing member does
as well. -/
theorem joinTreeCompletion_missingFaces_contains
    {F : ι → Set W} [Fintype ι]
    (S : Finset ι)
    [Nonempty {i : ι // i ∈ S}]
    (J : JoinTree
      (fun i : {t : ι // t ∈ S} => setBagPiece (F i.1)))
    {K : Set W} (hK : K.Nonempty)
    (hThird : ∀ x : W, x ∈ K →
      ∀ y : W, y ∈ K →
        ∃ z : W, z ∈ K ∧ z ≠ x ∧ z ≠ y)
    (faceBag : W → {i : ι // i ∈ S})
    (hFace : ∀ z : W, z ∈ K →
      ∀ x : W, x ∈ K → x ≠ z →
        x ∈ F (faceBag z).1) :
    ∃ i : ι, i ∈ S ∧ K ⊆ F i := by
  classical
  obtain ⟨i, hi⟩ :=
    J.missingFaces_contained_in_one_bag
      hK hThird faceBag hFace
  exact ⟨i.1, i.2, hi⟩

end StructuralRamsey.Girth
