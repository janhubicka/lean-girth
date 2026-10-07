import Girth.ForestReplayObstruction

/-!
# Algebraic ownership of non-support-edge pairs by B-copy leaves

In a pairwise-clean family of distinguished B-copies, two different
copies may contain the same pair of vertices only when that pair lies
on one whole common support edge. Thus a vertex pair which is not
co-contained in any support edge of one B-copy identifies that B-copy
uniquely among all distinguished copies.

This gives a second algebraic ownership constraint beyond the ordinary
two-point closure of individual support edges. It is a necessary part
of any faithful global successor-history evaluation.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

/-- Two distinct vertices of one piece which do not lie together on
a support edge cannot occur together in any other member of a
pairwise-clean family. -/
theorem unique_piece_containing_nonedge_pair
    (P : ι → HypergraphPiece W)
    (hAllowed : PairwiseAllowed P)
    {i j : ι} {x y : W}
    (hxy : x ≠ y)
    (hxi : x ∈ (P i).carrier) (hyi : y ∈ (P i).carrier)
    (hxj : x ∈ (P j).carrier) (hyj : y ∈ (P j).carrier)
    (hNonEdge :
      ∀ e : Set W, e ∈ (P i).edges →
        ¬ (x ∈ e ∧ y ∈ e)) :
    i = j := by
  by_contra hij
  rcases hAllowed hij with hSmall | ⟨e, heI, _heJ, heEq⟩
  · exact hxy
      (hSmall ⟨hxi, hxj⟩ ⟨hyi, hyj⟩)
  · have hxE : x ∈ e := by
      rw [← heEq]
      exact ⟨hxi, hxj⟩
    have hyE : y ∈ e := by
      rw [← heEq]
      exact ⟨hyi, hyj⟩
    exact hNonEdge e heI ⟨hxE, hyE⟩

end StructuralRamsey.Girth
