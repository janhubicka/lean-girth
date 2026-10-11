import Girth.LocalCoveredWitnessReduction
import Girth.ForestOneEdgeOwnerLocalTest

/-!
# Already-monochromatic active fibres with one physical edge

The recursive circulation proof has a separate case when the TRUE
active subsystem for a selected base A-edge contains just one physical
A-support edge. Even when the whole train target has many edges,
this individual active fibre may contain exactly one.

For edge colouring, any nonempty local copy family inside a target
with at most one physical edge is already monochromatic. Thus a
nontrivial local picture step is unnecessary in this case: the
construction can leave the old picture unchanged, retaining every
train, forest, girth and part parameter exactly.

This module formalizes the edge-colouring fact and the corresponding
trivial mixed finite-forest bound on the sole physical one-edge
piece. It does NOT yet formalize the entire identity picture-step
congruence or the well-founded recursive construction.
-/

namespace StructuralRamsey.Girth

universe v w
variable {X Y : Type v}

/-- Every edge colouring is already monochromatic on any chosen
designated copy when the entire target edge support contains at
most one physical edge. This is the precise edge-colouring reason
to skip the picture step on single-edge active fibres. -/
theorem strongSupportEdgeArrow_of_subsingleton_edge_target
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (hSource : H.Nonempty)
    (hFamily : ∃ f : StrongSupportEmbedding H K, f ∈ family)
    (hTarget : K.Subsingleton)
    (κ : Type w) :
    StrongSupportEdgeArrow H family κ := by
  intro χ
  obtain ⟨f, hf⟩ := hFamily
  obtain ⟨e, he⟩ := hSource
  let c : κ := χ ⟨f '' e, f.mappedEdge_mem e he⟩
  refine ⟨f, hf, c, ?_⟩
  intro e' he'
  have hEq :
      (⟨f '' e', f.mappedEdge_mem e' he'⟩ : K) =
        ⟨f '' e, f.mappedEdge_mem e he⟩ :=
    Subtype.ext (hTarget (f.mappedEdge_mem e' he') (f.mappedEdge_mem e he))
  exact congrArg χ hEq

/-- The two properties required of an elementary single-edge local
witness: its arrow is automatic, and its unique physical one-edge
support trivially satisfies every finite mixed forest bound. -/
theorem singleEdge_localWitness_arrow_and_forests
    {H : Set (Set X)} {K : Set (Set Y)}
    (family : Set (StrongSupportEmbedding H K))
    (hSource : H.Nonempty)
    (hFamily : ∃ f : StrongSupportEmbedding H K, f ∈ family)
    (hTarget : K.Subsingleton)
    (e : Set Y) (m : ℕ) (κ : Type w) :
    StrongSupportEdgeArrow H family κ ∧
    FiniteMixedForestThrough
      (fun P : HypergraphPiece Y => P = HypergraphPiece.oneEdge e)
      m := by
  exact ⟨
    strongSupportEdgeArrow_of_subsingleton_edge_target
      family hSource hFamily hTarget κ,
    finiteMixedForestThrough_singleEdge e m⟩

end StructuralRamsey.Girth
