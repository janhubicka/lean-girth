import Girth.TrainColouredOwnerSelectedStrong
import Girth.TrainFillingUniformEdgePresentation
import Girth.TrainFillingColouredOrderedEdgePresentation
import Girth.TrainColouredOwnerProjectionOrder

set_option Elab.async false

/-!
# Owner splitting preserves induced embeddings of the full uniform edge relation

The already verified owner-split modules construct a physical edge
bijection, the exact lift of each selected source edge, and the
projection from split vertices back to original vertices.

This file constructs the actual INDUCED relational embedding for the
uniform k-ary edge relation. It does not just map positive source
edges: reflection of every k-tuple follows by projecting any split
ambient edge back to a genuine old edge and invoking the selected
old induced embedding.

The source and target full edge families are not pruned. Source
vertices not on edges remain in the lift through the bottom owner
tag. Predicate and order preservation use the separate checked
owner-splitting interfaces and are the next packaging step.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe v
variable {V I W : Type v}
variable {H : ColouredEdgeOwnerSplit V I}
variable (S : ColouredOwnerSelectedCopy (W := W) H)

/-- Projecting the full lifted tuple carrier recovers the old embedded
tuple carrier, including any repeated tuple coordinates. -/
theorem ownerSplit_project_lifted_tuple_range {k : ℕ}
    (x : Fin k → W) :
    H.project '' Set.range (S.lift ∘ x) =
      Set.range (S.embedding ∘ x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (S.project_lift (x i)).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨S.lift (x i), ⟨i, rfl⟩, S.project_lift (x i)⟩

/-- The full image of any source edge under the vertex lift is
one actual split physical edge. Every endpoint, including those
with allowed predicate, is present. -/
theorem ownerSplit_lifted_source_tuple_edge {k : ℕ}
    (x : Fin k → W)
    (hx : Set.range x ∈ S.sourceEdges) :
    Set.range (S.lift ∘ x) ∈ Set.range H.splitEdge := by
  let e : S.SourceEdge := ⟨Set.range x, hx⟩
  refine ⟨S.physicalEdge e, ?_⟩
  calc
    H.splitEdge (S.physicalEdge e) =
        S.lift '' e.1 := (S.lift_source_edge e).symm
    _ = Set.range (S.lift ∘ x) := by
      ext z
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩

/-- Physical owner splitting preserves and reflects the FULL induced
uniform k-edge relation on a genuinely selected source copy.

The old relational embedding is explicitly required, but the new
induced embedding is constructed; no output map_rel_iff, new inducedness
or selected edge equality is supplied. -/
noncomputable def ownerSplit_lifted_uniformEmbedding (k : ℕ)
    (b : Embedding
       (uniformEdgeTarget k S.sourceEdges)
       (uniformEdgeTarget k H.edges))
    (hb : ∀ x : W, b x = S.embedding x) :
    Embedding
      (uniformEdgeTarget k S.sourceEdges)
      (uniformEdgeTarget k (Set.range H.splitEdge)) where
  toFun := S.lift
  injective := S.lift_injective
  map_rel_iff := by
    intro R x
    cases R
    change (Function.Injective (S.lift ∘ x) ∧
        Set.range (S.lift ∘ x) ∈ Set.range H.splitEdge) ↔
      (Function.Injective x ∧ Set.range x ∈ S.sourceEdges)
    constructor
    · intro hNew
      have hx : Function.Injective x := by
        intro i j hij
        exact hNew.1 (congrArg S.lift hij)
      have hEq : ((b : W → V) ∘ x) = S.embedding ∘ x := by
        funext i
        exact hb (x i)
      obtain ⟨f, hf⟩ := hNew.2
      have hOldRange : Set.range (S.embedding ∘ x) = f.1 := by
        calc
          Set.range (S.embedding ∘ x) =
              H.project '' Set.range (S.lift ∘ x) :=
            (ownerSplit_project_lifted_tuple_range S x).symm
          _ = H.project '' H.splitEdge f := by rw [hf]
          _ = f.1 := H.projection_splitEdge f
      have hOldMem : Set.range ((b : W → V) ∘ x) ∈ H.edges := by
        rw [hEq, hOldRange]
        exact f.2
      exact (b.map_rel_iff () x).mp
        ⟨b.injective.comp hx, hOldMem⟩
    · intro hSrc
      exact ⟨S.lift_injective.comp hSrc.1,
        ownerSplit_lifted_source_tuple_edge S x hSrc.2⟩

/-- The ORIGINAL induced coloured embedding already forces its own
unary colour preservation: take the source unary relation whose symbol
is exactly the colour of the chosen source vertex. No extra output
unary-predicate assumption is required. -/
theorem ownerSplit_oldEmbedding_colour
    [LinearOrder V] [LinearOrder W]
    (k : ℕ) (sourceColour : W → I)
    (b : Embedding
      (colouredOrderedEdgeTarget k S.sourceEdges sourceColour)
      (colouredOrderedEdgeTarget k H.edges H.predicate))
    (hb : ∀ w : W, b w = S.embedding w)
    (w : W) :
    H.predicate (S.embedding w) = sourceColour w := by
  have h :
      (colouredOrderedEdgeTarget k H.edges H.predicate).rel
          (.inl (.inr (sourceColour w)))
          ((b : W → V) ∘ (fun _ : Fin 1 => w)) := by
    apply (b.map_rel_iff (.inl (.inr (sourceColour w)))
      (fun _ : Fin 1 => w)).mpr
    change sourceColour w = sourceColour w
    rfl
  change H.predicate (b w) = sourceColour w at h
  rw [hb w] at h
  exact h

/-- Putting together the checked projection-first output order and
the actual induced uniform-edge lift constructs an induced embedding
of the COMPLETE coloured ordered edge language on a selected source.

The output's actual edge set is the full split physical edge family,
all unary predicates are derived from the original old embedding,
and every within-predicate order tuple is reflected. The only
separate order input is strict monotonicity of the genuine old
vertex map in its global chosen order: the projection-first output
order is available from the verified owner-splitting construction. -/
noncomputable def ownerSplit_lifted_colouredOrderedEmbedding
    {k : ℕ}
    [LinearOrder V] [LinearOrder W] [o : LinearOrder H.Vertex]
    (sourceColour : W → I)
    (b : Embedding
      (colouredOrderedEdgeTarget k S.sourceEdges sourceColour)
      (colouredOrderedEdgeTarget k H.edges H.predicate))
    (hb : ∀ w : W, b w = S.embedding w)
    (hOldMono : StrictMono S.embedding)
    (hProjectionOrder : ∀ a b : H.Vertex,
      H.project a < H.project b → @LT.lt H.Vertex o.toLT a b) :
    Embedding
      (colouredOrderedEdgeTarget k S.sourceEdges sourceColour)
      (@colouredOrderedEdgeTarget I H.Vertex k
        (Set.range H.splitEdge) H.newPredicate o) := by
  letI : LinearOrder H.Vertex := o
  let bUniform : Embedding
      (uniformEdgeTarget k S.sourceEdges)
      (uniformEdgeTarget k H.edges) := {
    toFun := b
    injective := b.injective
    map_rel_iff := by
      intro R x
      cases R
      exact b.map_rel_iff (.inl (.inl ())) x
  }
  have hbUniform : ∀ w : W, bUniform w = S.embedding w := hb
  let bLiftUniform := ownerSplit_lifted_uniformEmbedding S k bUniform hbUniform
  have hLiftMono : StrictMono S.lift := by
    intro x y hxy
    apply hProjectionOrder
    simpa only [S.project_lift] using hOldMono hxy
  refine {
    toFun := S.lift
    injective := S.lift_injective
    map_rel_iff := ?_
  }
  intro R x
  cases R with
  | inl R =>
      cases R with
      | inl _ =>
          exact bLiftUniform.map_rel_iff () x
      | inr colour =>
          change (Fin 1 → W) at x
          change H.newPredicate (S.lift (x 0)) = colour ↔
            sourceColour (x 0) = colour
          rw [H.selectedLift_preserves_predicate S (x 0),
            ownerSplit_oldEmbedding_colour S k sourceColour b hb (x 0)]
  | inr _ =>
      change (Fin 2 → W) at x
      change (H.newPredicate (S.lift (x 0)) =
        H.newPredicate (S.lift (x 1)) ∧
        S.lift (x 0) < S.lift (x 1)) ↔
        (sourceColour (x 0) = sourceColour (x 1) ∧ x 0 < x 1)
      have hxColour : H.newPredicate (S.lift (x 0)) =
          sourceColour (x 0) :=
        (H.selectedLift_preserves_predicate S (x 0)).trans
          (ownerSplit_oldEmbedding_colour S k sourceColour b hb (x 0))
      have hyColour : H.newPredicate (S.lift (x 1)) =
          sourceColour (x 1) :=
        (H.selectedLift_preserves_predicate S (x 1)).trans
          (ownerSplit_oldEmbedding_colour S k sourceColour b hb (x 1))
      rw [hxColour, hyColour]
      exact and_congr Iff.rfl hLiftMono.lt_iff_lt

end StructuralRamsey.Girth
