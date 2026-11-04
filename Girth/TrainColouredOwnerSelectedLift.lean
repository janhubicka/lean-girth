import Girth.TrainColouredEdgeOwnerSplit

set_option Elab.async false

/-!
# Selected-copy edge lift through physical owner splitting

A selected old copy carries a genuine embedding of vertices and a
physical carrier image for each source edge. At a forbidden predicate,
a source vertex meets at most one source edge. We construct its lifted
vertex with the corresponding ACTUAL physical edge token, using a bottom
tag only for vertices with no source edge.

The output is an injective vertex map. Each selected source physical edge
becomes exactly the split image of its old physical edge, not a subset,
and projection recovers the original selected embedding. No new output
embedding or new copy-edge image equality is assumed.

This does NOT yet establish the global selected-copy arrow or strongness;
those require transporting the source's full inducedness and the selected
family's controlled intersections, and remain separate.
-/

namespace StructuralRamsey.Girth

universe v
variable {V I W : Type v} (H : ColouredEdgeOwnerSplit V I)

/-- The exact source-edge and physical-carrier data of one selected copy
in the original coloured witness. Its unique-edge-at-forbidden-parts
property is precisely the manuscript's source hypothesis. -/
structure ColouredOwnerSelectedCopy where
  sourceEdges : Set (Set W)
  embedding : W ↪ V
  physicalEdge : {e : Set W // e ∈ sourceEdges} → H.OldEdge
  edge_image : ∀ e, (physicalEdge e).1 = embedding '' e.1
  forbidden_unique : ∀ (w : W)
    (e f : {e : Set W // e ∈ sourceEdges}),
    H.predicate (embedding w) ∉ H.allowed →
    w ∈ e.1 → w ∈ f.1 → e = f

namespace ColouredOwnerSelectedCopy

variable {H} (S : ColouredOwnerSelectedCopy H W)

abbrev SourceEdge (S : ColouredOwnerSelectedCopy H W) :=
  {e : Set W // e ∈ S.sourceEdges}

/-- Lift one selected source vertex through owner-tagged incidence
splitting. The forbidden-predicate owner is an actual physical edge. -/
noncomputable def lift (w : W) : H.Vertex := by
  classical
  exact if hAllow : H.predicate (S.embedding w) ∈ H.allowed then
    Sum.inl (S.embedding w)
  else if hInc : ∃ e : S.SourceEdge, w ∈ e.1 then
    Sum.inr (S.embedding w, Sum.inl
      (S.physicalEdge (Classical.choose hInc)))
  else
    Sum.inr (S.embedding w, Sum.inr PUnit.unit)

/-- Every source edge fixes the unique forbidden-predicate incidence
owner at each of its endpoints. -/
theorem lift_on_source_edge
    (e : S.SourceEdge) (w : W) (hw : w ∈ e.1) :
    S.lift w = H.place (S.physicalEdge e) (S.embedding w) := by
  classical
  by_cases hAllow : H.predicate (S.embedding w) ∈ H.allowed
  · simp [lift, ColouredEdgeOwnerSplit.place, hAllow]
  · have hInc : ∃ f : S.SourceEdge, w ∈ f.1 := ⟨e, hw⟩
    have hChosen : Classical.choose hInc = e :=
      S.forbidden_unique w (Classical.choose hInc) e
        hAllow (Classical.choose_spec hInc) hw
    simp [lift, ColouredEdgeOwnerSplit.place, hAllow, hInc, hChosen]

/-- Projection discards precisely the incidence token, not the
original vertex of the selected copy. -/
@[simp] theorem project_lift (w : W) :
    H.project (S.lift w) = S.embedding w := by
  classical
  by_cases hAllow : H.predicate (S.embedding w) ∈ H.allowed
  · simp [lift, ColouredEdgeOwnerSplit.project, hAllow]
  · by_cases hInc : ∃ e : S.SourceEdge, w ∈ e.1
    · simp [lift, ColouredEdgeOwnerSplit.project, hAllow, hInc]
    · simp [lift, ColouredEdgeOwnerSplit.project, hAllow, hInc]

/-- Lifting never identifies two different vertices of a selected
ordered source, regardless of the number of incident forbidden edges. -/
theorem lift_injective : Function.Injective S.lift := by
  intro x y h
  apply S.embedding.injective
  have hp := congrArg H.project h
  simpa only [S.project_lift] using hp

/-- The ENTIRE selected source edge is precisely its owner's split
physical edge. This is the key identity for transporting the edge
colouring and strongly induced selected copies. -/
theorem lift_source_edge (e : S.SourceEdge) :
    S.lift '' e.1 = H.splitEdge (S.physicalEdge e) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [S.lift_on_source_edge e w hw]
    refine ⟨S.embedding w, ?_, rfl⟩
    rw [S.edge_image e]
    exact ⟨w, hw, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [S.edge_image e] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    subst x
    exact ⟨w, hw, S.lift_on_source_edge e w hw⟩

/-- The lifted selected physical edge map is injective: old physical
carrier equality is reflected to source carrier equality by the
injective selected embedding. -/
theorem physicalEdge_injective :
    Function.Injective S.physicalEdge := by
  intro e f hef
  apply Subtype.ext
  ext w
  constructor
  · intro hw
    have hImage : S.embedding w ∈ S.embedding '' f.1 := by
      rw [← S.edge_image f, ← hef, S.edge_image e]
      exact ⟨w, hw, rfl⟩
    obtain ⟨w', hw', heq⟩ := hImage
    have hww : w = w' := S.embedding.injective heq.symm
    simpa only [hww] using hw'
  · intro hw
    have hImage : S.embedding w ∈ S.embedding '' e.1 := by
      rw [← S.edge_image e, hef, S.edge_image f]
      exact ⟨w, hw, rfl⟩
    obtain ⟨w', hw', heq⟩ := hImage
    have hww : w = w' := S.embedding.injective heq.symm
    simpa only [hww] using hw'

end ColouredOwnerSelectedCopy
end StructuralRamsey.Girth
