import Girth.TrainColouredOwnerSelectedStrong
import Girth.TrainFillingUniformEdgePresentation

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
            (S.ownerSplit_project_lifted_tuple_range x).symm
          _ = H.project '' H.splitEdge f := by rw [hf]
          _ = f.1 := H.projection_splitEdge f
      have hOldMem : Set.range ((b : W → V) ∘ x) ∈ H.edges := by
        rw [hEq, hOldRange]
        exact f.2
      exact (b.map_rel_iff () x).mp
        ⟨b.injective.comp hx, hOldMem⟩
    · intro hSrc
      exact ⟨S.lift_injective.comp hSrc.1,
        S.ownerSplit_lifted_source_tuple_edge x hSrc.2⟩

end StructuralRamsey.Girth
