import Girth.TrainColouredOwnerSelectedLift

set_option Elab.async false

/-!
# Strongness and small intersections survive owner-incidence splitting

The previous selected-copy lift has exact split-edge images and an
injective vertex map. Here we preserve STRONGNESS and the empty/singleton
part of pairwise-copy intersection control.

Projection to the old vertices is injective on each ACTUAL split edge.
Therefore two distinct contacts between one split ambient edge and one
lifted selected copy give two distinct old contacts. Old strongness
forces that old ambient edge to be one of the selected old physical
edges, whose entire split image has already been proved to equal a
selected source edge image.

Two lifted selected copies also cannot create new intersections:
projection sends their intersection into the old intersection, and
projection is injective on either lifted copy. In particular empty and
singleton old intersections remain empty and singleton.

The remaining common-whole-edge intersection case, inducedness of the
full ordered relational expansion, and the Ramsey-arrow transfer are
separate from these no-new-contact lemmas.
-/

namespace StructuralRamsey.Girth

universe v

namespace ColouredEdgeOwnerSplit

variable {V I : Type v} (H : ColouredEdgeOwnerSplit V I)

/-- On a single split physical edge, projection is injective: one
old endpoint can occur at most once with that edge's owner token. -/
theorem project_injective_on_splitEdge
    (f : H.OldEdge) {z w : H.Vertex}
    (hz : z ∈ H.splitEdge f) (hw : w ∈ H.splitEdge f)
    (hProj : H.project z = H.project w) : z = w := by
  obtain ⟨x, _hx, hxz⟩ := hz
  obtain ⟨y, _hy, hyw⟩ := hw
  have hxy : x = y := by
    have heq :
        H.project (H.place f x) = H.project (H.place f y) := by
      calc
        H.project (H.place f x) = H.project z :=
          congrArg H.project hxz
        _ = H.project w := hProj
        _ = H.project (H.place f y) :=
          congrArg H.project hyw.symm
    simpa only [H.project_place] using heq
  calc
    z = H.place f x := hxz.symm
    _ = H.place f y := congrArg (H.place f) hxy
    _ = w := hyw

end ColouredEdgeOwnerSplit

namespace ColouredOwnerSelectedCopy

variable {V I W : Type v} {H : ColouredEdgeOwnerSplit V I}
variable (S : ColouredOwnerSelectedCopy (W := W) H)

/-- Projection is injective on each lifted selected-copy vertex
carrier, because its composition with the lift is the injective
original selected vertex embedding. -/
theorem project_injective_on_lift_range
    {z w : H.Vertex}
    (hz : z ∈ Set.range S.lift)
    (hw : w ∈ Set.range S.lift)
    (hProj : H.project z = H.project w) : z = w := by
  obtain ⟨x, hx⟩ := hz
  obtain ⟨y, hy⟩ := hw
  have hxy : x = y := by
    apply S.embedding.injective
    have hp : H.project (S.lift x) = H.project (S.lift y) := by
      calc
        H.project (S.lift x) = H.project z := congrArg H.project hx
        _ = H.project w := hProj
        _ = H.project (S.lift y) := congrArg H.project hy.symm
    simpa only [S.project_lift] using hp
  calc
    z = S.lift x := hx.symm
    _ = S.lift y := congrArg S.lift hxy
    _ = w := hy

/-- Old strongness, expressed ONLY on genuine original physical edges,
forces strongness of every lifted selected copy in the SPLIT ambient
hypergraph. No output edge ownership or output strongness is supplied. -/
theorem selected_strong_of_old
    (hOldStrong : ∀ (f : H.OldEdge) (x y : V),
      x ≠ y → x ∈ f.1 → y ∈ f.1 →
      x ∈ Set.range S.embedding → y ∈ Set.range S.embedding →
      ∃ a : S.SourceEdge, S.physicalEdge a = f)
    (f : H.OldEdge) (z w : H.Vertex)
    (hzw : z ≠ w)
    (hzEdge : z ∈ H.splitEdge f) (hwEdge : w ∈ H.splitEdge f)
    (hzCopy : z ∈ Set.range S.lift)
    (hwCopy : w ∈ Set.range S.lift) :
    ∃ a : S.SourceEdge, S.physicalEdge a = f := by
  have hProjNe : H.project z ≠ H.project w := by
    intro h
    exact hzw (H.project_injective_on_splitEdge f hzEdge hwEdge h)
  have hzOldEdge : H.project z ∈ f.1 := by
    have hm : H.project z ∈ H.project '' H.splitEdge f :=
      ⟨z, hzEdge, rfl⟩
    rw [H.projection_splitEdge f] at hm
    exact hm
  have hwOldEdge : H.project w ∈ f.1 := by
    have hm : H.project w ∈ H.project '' H.splitEdge f :=
      ⟨w, hwEdge, rfl⟩
    rw [H.projection_splitEdge f] at hm
    exact hm
  have hzOldCopy : H.project z ∈ Set.range S.embedding := by
    obtain ⟨x, hx⟩ := hzCopy
    exact ⟨x, (S.project_lift x).symm.trans (congrArg H.project hx)⟩
  have hwOldCopy : H.project w ∈ Set.range S.embedding := by
    obtain ⟨y, hy⟩ := hwCopy
    exact ⟨y, (S.project_lift y).symm.trans (congrArg H.project hy)⟩
  exact hOldStrong f (H.project z) (H.project w)
    hProjNe hzOldEdge hwOldEdge hzOldCopy hwOldCopy

/-- Every split image of an old selected source edge is wholly in
the lifted selected vertex carrier. This is literal image equality,
not a containment hypothesis on the output. -/
theorem split_selected_edge_subset_copy (a : S.SourceEdge) :
    H.splitEdge (S.physicalEdge a) ⊆ Set.range S.lift := by
  intro z hz
  rw [← S.lift_source_edge a] at hz
  obtain ⟨x, _hx, hxz⟩ := hz
  exact ⟨x, hxz⟩

/-- Projection of the intersection of two genuinely lifted selected
copies is contained in their original physical intersection. -/
theorem lifted_pair_intersection_projects
    {Z : Type v} (T : ColouredOwnerSelectedCopy (W := Z) H) :
    H.project '' (Set.range S.lift ∩ Set.range T.lift) ⊆
      Set.range S.embedding ∩ Set.range T.embedding := by
  rintro y ⟨z, ⟨hzS, hzT⟩, hzy⟩
  obtain ⟨x, hx⟩ := hzS
  obtain ⟨w, hw⟩ := hzT
  refine ⟨?_, ?_⟩
  · exact ⟨x, (S.project_lift x).symm.trans
      ((congrArg H.project hx).trans hzy)⟩
  · exact ⟨w, (T.project_lift w).symm.trans
      ((congrArg H.project hw).trans hzy)⟩

/-- An old pairwise singleton intersection cannot become a multi-vertex
intersection after incidence splitting. -/
theorem lifted_pair_intersection_subsingleton
    {Z : Type v} (T : ColouredOwnerSelectedCopy (W := Z) H)
    (hOldSmall :
      (Set.range S.embedding ∩ Set.range T.embedding).Subsingleton) :
    (Set.range S.lift ∩ Set.range T.lift).Subsingleton := by
  intro z hz w hw
  have hzProjected : H.project z ∈
      Set.range S.embedding ∩ Set.range T.embedding :=
    S.lifted_pair_intersection_projects T ⟨z, hz, rfl⟩
  have hwProjected : H.project w ∈
      Set.range S.embedding ∩ Set.range T.embedding :=
    S.lifted_pair_intersection_projects T ⟨w, hw, rfl⟩
  exact S.project_injective_on_lift_range
    hz.1 hw.1 (hOldSmall hzProjected hwProjected)

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
