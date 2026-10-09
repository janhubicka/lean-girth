import Girth.ForestTwoCopyPortGlue
import Mathlib.Tactic

/-!
# Exact obstruction to a forest of two privately duplicated B-copies

For the explicit two-copy construction glued along S, the family is
a forest if and only if S is at most a vertex or one complete A-edge
of the original B-piece. There are no hidden geometric hypotheses:
the copies are physical images inside W × Bool and their intersection
is precisely the prescribed separator.

In particular duplicating a moving B-copy over two incomparable old
contacts which are not covered by one intrinsic A-edge yields a
nonforest pair. This is the finite obstruction needed *after*
a carrier-faithful pre-birth split has been realized. The theorem
does not assert that every such split can occur inside the valid
global Ramsey/partite reservoir.
-/

namespace StructuralRamsey.Girth

universe v
variable {W : Type v}

/-- In the explicit two-copy model, the intersection of the two
whole B-carriers is exactly the image of S when S is contained in P. -/
theorem twoCopyPort_piece_inter
    (P : HypergraphPiece W) (S : Set W)
    (hSub : S ⊆ P.carrier) :
    (P.map (twoCopyPortLeft S)).carrier ∩
      (P.map (twoCopyPortRight S)).carrier =
      (twoCopyPortLeft S) '' S := by
  change (twoCopyPortLeft S) '' P.carrier ∩
    (twoCopyPortRight S) '' P.carrier =
      (twoCopyPortLeft S) '' S
  rw [twoCopyPort_images_inter]
  congr 1
  apply Set.Subset.antisymm
  · exact Set.inter_subset_right
  · intro x hx
    exact ⟨hSub hx, hx⟩

/-- Injectivity of the explicitly tagged left copy reflects equality
of all image subsets. -/
theorem twoCopyPort_left_image_eq_iff
    (S A B : Set W) :
    (twoCopyPortLeft S) '' A = (twoCopyPortLeft S) '' B ↔
      A = B := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      have him : twoCopyPortLeft S x ∈
          (twoCopyPortLeft S) '' B := by
        rw [← h]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := him
      have hEq : x = y := (twoCopyPortLeft S).injective hxy
      simpa [hEq] using hy
    · intro x hx
      have him : twoCopyPortLeft S x ∈
          (twoCopyPortLeft S) '' A := by
        rw [h]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := him
      have hEq : x = y := (twoCopyPortLeft S).injective hxy
      simpa [hEq] using hy
  · intro h
    rw [h]

/-- A permitted intersection of the actual two B-copies forces
their complete shared separator to be at most one vertex or one
source A-support edge. Thus our sufficient condition is exact. -/
theorem twoCopyPort_allowedIntersection_iff
    (P : HypergraphPiece W) (S : Set W)
    (hSub : S ⊆ P.carrier) :
    AllowedIntersection
      (P.map (twoCopyPortLeft S))
      (P.map (twoCopyPortRight S)) ↔
      S.Subsingleton ∨ S ∈ P.edges := by
  constructor
  · intro hAllowed
    have hCap := twoCopyPort_piece_inter P S hSub
    rcases hAllowed with hSmall | ⟨e, heL, _, hIntersection⟩
    · left
      intro x hx y hy
      apply (twoCopyPortLeft S).injective
      have hSmallImage :
          ((twoCopyPortLeft S) '' S).Subsingleton := by
        rw [← hCap]
        exact hSmall
      exact hSmallImage ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    · obtain ⟨a, ha, hImageA⟩ := heL
      have hImageEq :
          (twoCopyPortLeft S) '' S =
            (twoCopyPortLeft S) '' a := by
        calc
          (twoCopyPortLeft S) '' S =
              (P.map (twoCopyPortLeft S)).carrier ∩
                (P.map (twoCopyPortRight S)).carrier := hCap.symm
          _ = e := hIntersection
          _ = (twoCopyPortLeft S) '' a := hImageA
      have hS : S = a :=
        (twoCopyPort_left_image_eq_iff S S a).mp hImageEq
      exact Or.inr (hS ▸ ha)
  · intro hGood
    exact twoCopyPort_allowedIntersection P S hSub hGood

/-- The geometric two-copy forest test is EXACT: its two-member
family is a forest if and only if the glued separator is allowed.
Its join tree is automatic; only the local intersection can fail. -/
theorem twoCopyPort_forest_iff
    (P : HypergraphPiece W) (S : Set W)
    (hSub : S ⊆ P.carrier) :
    ForestOfCopies
      (sumPieces
        (fun _ : PUnit.{v+1} => P.map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} => P.map (twoCopyPortRight S))) ↔
      S.Subsingleton ∨ S ∈ P.edges := by
  constructor
  · intro hForest
    have hCross : AllowedIntersection
        (P.map (twoCopyPortLeft S))
        (P.map (twoCopyPortRight S)) := by
      exact hForest.pairwiseAllowed
        (show (Sum.inl PUnit.unit : PUnit.{v+1} ⊕ PUnit.{v+1}) ≠
          Sum.inr PUnit.unit by decide)
    exact (twoCopyPort_allowedIntersection_iff P S hSub).mp hCross
  · intro hGood
    exact twoCopyPort_forest P S hSub hGood

/-- With at least two incomparable boundary vertices and no whole
old A-edge equal to S, the two physical B-copies cannot form a
forest despite each being an exact injective image of B. -/
theorem twoCopyPort_nonforest_of_forbiddenSeparator
    (P : HypergraphPiece W) (S : Set W)
    (hSub : S ⊆ P.carrier)
    (hLarge : ¬ S.Subsingleton)
    (hNoA : S ∉ P.edges) :
    ¬ ForestOfCopies
      (sumPieces
        (fun _ : PUnit.{v+1} => P.map (twoCopyPortLeft S))
        (fun _ : PUnit.{v+1} => P.map (twoCopyPortRight S))) := by
  intro hForest
  rcases (twoCopyPort_forest_iff P S hSub).mp hForest with hs | he
  · exact hLarge hs
  · exact hNoA he

end StructuralRamsey.Girth
