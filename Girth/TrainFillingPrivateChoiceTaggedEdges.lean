import Girth.TrainFillingPrivateChoiceTaggedTarget

set_option Elab.async false

/-!
# Exactly the original selected physical edges inside the tagged M

For every selected EHN choice c, its SummandPrivateTemplate gives
one local A-support edge for each old first wagon. The previous
module constructs the selected filled physical edge inside M_c[X]
and proves its full carrier is the original old edge carrier.

Now tag that whole component by c. The result is an ACTUAL
physical edge in the complete heterogeneous G0, with literal
vertex carrier τ_c[e] for the tagged original vertex embedding
τ_c : V(T) -> V(M). This is the exact source-side identity needed
for the manuscript's corrected final formula
  ι_{j[bar f_{c,p}]}[s_p[e]] = j[τ_c[e]].

The particular source train relation and ordered predicates have
not been identified with T in this module; they remain the
separate global train-embedding obligations. No output arrow
or girth is taken as an assumption here.

Candidate source, pending Lean compilation.
-/

namespace StructuralRamsey.Girth.IndexedPrivateChoice

universe v
variable {C V P X : Type v}

/-- Each choice c has its own private template data, but all
choices act on the SAME original first-wagon vertex set V and
all use the SAME complete ambient X vertex type. -/
variable (S : C → SummandPrivateTemplate V P X)

private abbrev U : C → PrivateWagonInput V P X :=
  fun c => (S c).toPrivateWagonInput

/-- The original local first-wagon edge of c is an actual selected
physical heterogeneous edge of G0, retaining BOTH the c and p
occurrence labels. -/
noncomputable def selectedTaggedOriginalEdge
    (c : C) (e : (S c).OriginalEdge) :
    Edge (U S) :=
  tagEdge (U S) c ((S c).originalSelectedEdge e)

/-- The selected original physical edge is in the correct component
of the actual target family, rather than being a phantom edge set. -/
theorem selectedTaggedOriginalEdge_mem_target
    (c : C) (e : (S c).OriginalEdge) :
    selectedTaggedOriginalEdge S c e ∈ targetEdges (U S) c := by
  exact ⟨(S c).originalSelectedEdge e,
    (S c).originalSelectedEdge_mem_target e, rfl⟩

/-- Literal carrier identity in the actual tagged heterogeneous M.
Every original first-wagon edge maps onto exactly its old vertex
carrier under τ_c, including all shared original vertices.
No private vertex occurs in a selected original edge. -/
theorem selectedTaggedOriginalEdge_carrier
    (c : C) (e : (S c).OriginalEdge) :
    edgeCarrier (U S) (selectedTaggedOriginalEdge S c e) =
      (originalTargetVertexEmbedding (U S) c) ''
        (Subtype.val '' e.2.1) := by
  let Uc := (S c).toPrivateWagonInput
  have hOld := (S c).originalSelectedEdge_carrier e
  calc
    edgeCarrier (U S) (selectedTaggedOriginalEdge S c e) =
        (tagVertex (U S) c) ''
          Uc.edgeCarrier ((S c).originalSelectedEdge e) := rfl
    _ = (tagVertex (U S) c) ''
        ((Sum.inl : V → Uc.Vertex) '' (Subtype.val '' e.2.1)) :=
          congrArg (fun A : Set Uc.Vertex =>
            (tagVertex (U S) c) '' A) hOld
    _ = (originalTargetVertexEmbedding (U S) c) ''
        (Subtype.val '' e.2.1) := by
          ext z
          constructor
          · rintro ⟨w, ⟨x, hx, hw⟩, hz⟩
            exact ⟨x, hx, by
              change tagVertex (U S) c (Sum.inl x) = z
              rw [← hw]
              exact hz⟩
          · rintro ⟨x, hx, hz⟩
            exact ⟨Sum.inl x, ⟨x, hx, rfl⟩, by
              change tagVertex (U S) c (Sum.inl x) = z
              exact hz⟩

end StructuralRamsey.Girth.IndexedPrivateChoice
