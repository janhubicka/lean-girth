import Girth.TrainColouredOwnerSelectedStrong

set_option Elab.async false

/-!
# Whole-edge intersections are exact under owner-incidence splitting

The checked selected-copy lift #790 keeps each genuine source physical
edge as precisely its owner's split edge. The checked strongness and
projection modules #810 show no new intersections appear and that
projection is injective on the lifted selected copy.

If two old selected copies intersect only inside one common OLD edge f,
and f belongs as a selected physical source edge to BOTH copies, every
vertex in their split-copy intersection must carry the tag of f (or be
an allowed-predicate vertex). Thus the new intersection is EXACTLY
the full physical split image of f.

We derive this from the input old selected edge memberships and old
intersection bound; no output whole-edge intersection premise is used.
The remaining prescribed A1 lemma still requires full ordered induced
relational lifting and final Ramsey-arrow assembly.
-/

namespace StructuralRamsey.Girth

universe v

namespace ColouredOwnerSelectedCopy

variable {V I W : Type v} {H : ColouredEdgeOwnerSplit V I}
variable (S : ColouredOwnerSelectedCopy (W := W) H)

/-- Every lifted selected vertex whose old projection lies in an
actual old source edge is literally placed with THAT edge owner. -/
theorem lift_eq_place_of_old_edge
    (a : S.SourceEdge) (z : H.Vertex)
    (hz : z ∈ Set.range S.lift)
    (hProj : H.project z ∈ (S.physicalEdge a).1) :
    z = H.place (S.physicalEdge a) (H.project z) := by
  obtain ⟨x, rfl⟩ := hz
  have hxOld : S.embedding x ∈ (S.physicalEdge a).1 := by
    simpa only [S.project_lift] using hProj
  rw [S.edge_image a] at hxOld
  obtain ⟨y, hy, hyx⟩ := hxOld
  have hxy : y = x := S.embedding.injective hyx
  have hx : x ∈ a.1 := by simpa only [hxy] using hy
  simpa only [S.project_lift] using S.lift_on_source_edge a x hx

/-- If the old common carrier is contained in a shared physical edge
which is selected in BOTH copies, then the exact lifted intersection
is its whole split edge, with no new or missing endpoints. -/
theorem lifted_intersection_eq_splitEdge
    {Z : Type v} (T : ColouredOwnerSelectedCopy (W := Z) H)
    (f : H.OldEdge)
    (hOldInter :
      Set.range S.embedding ∩ Set.range T.embedding ⊆ f.1)
    (hS : f ∈ Set.range S.physicalEdge)
    (hT : f ∈ Set.range T.physicalEdge) :
    Set.range S.lift ∩ Set.range T.lift = H.splitEdge f := by
  have hSsub : H.splitEdge f ⊆ Set.range S.lift := by
    obtain ⟨a, ha⟩ := hS
    rw [← ha]
    exact S.split_selected_edge_subset_copy a
  have hTsub : H.splitEdge f ⊆ Set.range T.lift := by
    obtain ⟨a, ha⟩ := hT
    rw [← ha]
    exact T.split_selected_edge_subset_copy a
  ext z
  constructor
  · intro hz
    have hzOld : H.project z ∈ f.1 := by
      apply hOldInter
      exact S.lifted_pair_intersection_projects T ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := hS
    have hOwner : H.project z ∈ (S.physicalEdge a).1 := by
      simpa only [ha] using hzOld
    have hPlace : z = H.place (S.physicalEdge a) (H.project z) :=
      S.lift_eq_place_of_old_edge a z hz.1 hOwner
    rw [ha] at hPlace
    exact ⟨H.project z, hzOld, hPlace.symm⟩
  · intro hz
    exact ⟨hSsub hz, hTsub hz⟩

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
