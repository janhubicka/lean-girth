import Girth.LocalForestPieces
import Girth.ForestSingleEdge

/-!
# A genuinely multi-edge gluing source cannot equal one core edge

The mixed-owner local forest bridge separates designated gluing-copy
support pieces from exceptional ambient one-edge pieces.  Its
injectivity argument needs the former not to be one-edge pieces.

This follows directly from any two distinct edges of the source:
a strong support embedding is injective, so the two image edges are
distinct.  No additional girth or coverage assumption is involved.
This is the precise support-theoretic reason the one-edge target is
handled separately in the manuscript's recursion.
-/

namespace StructuralRamsey.Girth

universe v
variable {X Y : Type v}

/-- Two different support edges force a piece not to be one-edge. -/
theorem HypergraphPiece.not_isOneEdge_of_twoEdges
    (F : HypergraphPiece Y)
    (e f : Set Y)
    (he : e ∈ F.edges) (hf : f ∈ F.edges)
    (hne : e ≠ f) :
    ¬F.IsOneEdge := by
  intro hOne
  change F.edges = {F.carrier} at hOne
  have heEq : e = F.carrier := by
    rw [hOne] at he
    simpa using he
  have hfEq : f = F.carrier := by
    rw [hOne] at hf
    simpa using hf
  exact hne (heEq.trans hfEq.symm)

/-- Any two distinct source edges remain distinct under an injective
strong support embedding, so the entire source copy has more than
one support edge. -/
theorem StrongSupportEmbedding.supportPiece_notIsOneEdge_of_twoSourceEdges
    {H : Set (Set X)} {K : Set (Set Y)}
    (g : StrongSupportEmbedding H K)
    (e f : Set X)
    (he : e ∈ H) (hf : f ∈ H)
    (hne : e ≠ f) :
    ¬g.supportPiece.IsOneEdge := by
  have heImg : g '' e ∈ g.supportPiece.edges := ⟨e, he, rfl⟩
  have hfImg : g '' f ∈ g.supportPiece.edges := ⟨f, hf, rfl⟩
  have hImgDiff : g '' e ≠ g '' f := by
    intro hImg
    apply hne
    ext x
    constructor
    · intro hx
      have hMem : g x ∈ g '' f := by
        rw [← hImg]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hEq⟩ := hMem
      have hYX : y = x := g.injective hEq
      simpa [hYX] using hy
    · intro hx
      have hMem : g x ∈ g '' e := by
        rw [hImg]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hEq⟩ := hMem
      have hYX : y = x := g.injective hEq
      simpa [hYX] using hy
  exact g.supportPiece.not_isOneEdge_of_twoEdges
    (g '' e) (g '' f) heImg hfImg hImgDiff

/-- Every gluing copy inherits the non-one-edge property from a
fixed source containing at least two distinct support edges. -/
theorem strongSupportFamily_notIsOneEdge
    {H : Set (Set X)} {K : Set (Set Y)}
    {I : Type v}
    (family : I → StrongSupportEmbedding H K)
    (e f : Set X) (he : e ∈ H) (hf : f ∈ H)
    (hne : e ≠ f) :
    ∀ i : I, ¬(family i).supportPiece.IsOneEdge :=
  fun i =>
    (family i).supportPiece_notIsOneEdge_of_twoSourceEdges
      e f he hf hne

end StructuralRamsey.Girth
