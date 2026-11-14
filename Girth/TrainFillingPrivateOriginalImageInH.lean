import Girth.TrainFillingPrivateChoiceTaggedEdges
import Girth.TrainFillingIndexedParentwiseRealization

set_option Elab.async false

/-!
# The literal original target edge inside each selected parent in H

Given the checked global ParentwiseRealization interface, an old
parent i realizes the entire choice-indexed heterogeneous G0,
with exact complete physical edge carriers in the ambient H.

For an actual original first-wagon edge e, the newly constructed
selectedTaggedOriginalEdge S c e lies in the original target
of choice c and its carrier is exactly τ_c[e].

Thus after applying the SAME selected parent vertex map j_i,
the image of that original edge is exactly (j_i ∘ τ_c)[e].
This is the rigorous physical-edge form of the manuscript's
corrected tagged formula, and removes its former ill-typed j[e].

It does NOT assert that a general arbitrary target T is
identified with the sum of the local A-support edge families:
that identification and all original train relations/partite
orders remain obligations of the cutoff-two call site.

Candidate source until Lean has compiled the exact branch.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X Q GV GE I GQ : Type v}
variable (S : C → SummandPrivateTemplate V P X)
variable (parent : P → Q)
variable (D : OrderOneData GV GE I GQ)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (S c).toPrivateWagonInput

/-- The ACTUAL original physical edge lies in the designated
(target old parent i, EHN choice c) edge family. -/
theorem ParentwiseRealization.originalTaggedEdge_mem_target
    (R : ParentwiseRealization (U S) parent D)
    (i : I) (c : C) (e : (S c).OriginalEdge) :
    R.edge i (selectedTaggedOriginalEdge S c e) ∈
      R.targetEdges (i,c) := by
  exact ⟨selectedTaggedOriginalEdge S c e,
    selectedTaggedOriginalEdge_mem_target S c e, rfl⟩

/-- The physical edge of the original T under the chosen
label (i,c) has precisely the carrier obtained by first
tagging original vertices with c, then applying the SAME
old selected parent i. No untagged original T vertex is
passed to a map defined only on the vertices of M. -/
theorem ParentwiseRealization.originalTaggedEdge_carrier
    (R : ParentwiseRealization (U S) parent D)
    (i : I) (c : C) (e : (S c).OriginalEdge) :
    D.edgeCarrier (R.edge i (selectedTaggedOriginalEdge S c e)) =
      (fun v : V =>
        R.vertex i (originalTargetVertexEmbedding (U S) c v)) ''
          (Subtype.val '' e.2.1) := by
  have hSelected :=
    selectedTaggedOriginalEdge_carrier S c e
  calc
    D.edgeCarrier (R.edge i (selectedTaggedOriginalEdge S c e)) =
        (R.vertex i) ''
          edgeCarrier (U S) (selectedTaggedOriginalEdge S c e) :=
      R.edgeCarrier_eq i (selectedTaggedOriginalEdge S c e)
    _ = (R.vertex i) ''
        ((originalTargetVertexEmbedding (U S) c) ''
          (Subtype.val '' e.2.1)) :=
      congrArg (fun E : Set (Vertex (U S)) =>
        (R.vertex i) '' E) hSelected
    _ = (fun v : V =>
        R.vertex i (originalTargetVertexEmbedding (U S) c v)) ''
          (Subtype.val '' e.2.1) := by
      ext z
      constructor
      · rintro ⟨w, ⟨v, hv, hw⟩, hz⟩
        exact ⟨v, hv, by
          change R.vertex i
            (originalTargetVertexEmbedding (U S) c v) = z
          rw [hw]
          exact hz⟩
      · rintro ⟨v, hv, hz⟩
        exact ⟨originalTargetVertexEmbedding (U S) c v,
          ⟨v, hv, rfl⟩, hz⟩

end StructuralRamsey.Girth.IndexedPrivateChoice
