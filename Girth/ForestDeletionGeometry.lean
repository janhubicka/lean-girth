import Girth.ForestLeafDeletion
import Girth.ForestSingleEdge

/-! # Geometry after deleting a join-tree member

The key observation for deleting a one-edge member is that any vertex shared
between two different components of the join tree after deletion must have
occurred in the deleted member.  This isolates the only possible cross-component
overlap before the one-edge intersection dichotomy is used.
-/

namespace StructuralRamsey.Girth

universe v
variable {W ι : Type v}

namespace JoinTree

/-- If two surviving pieces share a vertex but become unreachable after
deleting `center` from the join tree, then that shared vertex belongs to the
deleted piece. -/
theorem mem_center_of_shared_not_reachable_after_delete
    {F : ι → HypergraphPiece W}
    (J : JoinTree F)
    {center i j : ι}
    (hi : i ≠ center) (hj : j ≠ center)
    {x : W}
    (hxi : x ∈ (F i).carrier)
    (hxj : x ∈ (F j).carrier)
    (hnreach :
      ¬ (J.tree.induce (({center} : Set ι)ᶜ)).Reachable
        ⟨i, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩
        ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj⟩) :
    x ∈ (F center).carrier := by
  by_contra hxc
  let occ : Set ι := {k : ι | x ∈ (F k).carrier}
  let iOcc : occ := ⟨i, hxi⟩
  let jOcc : occ := ⟨j, hxj⟩
  have hreach :
      (J.tree.induce occ).Reachable iOcc jOcc := by
    simpa [occ, iOcc, jOcc] using J.running x iOcc jOcc
  let phi :
      (J.tree.induce occ) →g
        (J.tree.induce (({center} : Set ι)ᶜ)) where
    toFun z :=
      ⟨z.1, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hz
        subst hz
        exact hxc z.2⟩
    map_rel' := by
      intro a b hab
      exact hab
  have hm := hreach.map phi
  apply hnreach
  simpa [phi, iOcc, jOcc] using hm

end JoinTree

end StructuralRamsey.Girth
