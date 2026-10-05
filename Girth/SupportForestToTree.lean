import Girth.SupportedCopyForestInduction
import Girth.Forest

/-! # From support forests to supported B-copy forests

This module identifies the manuscript's hypergraph forest condition on the
A-supports of B-copies with the three relational overlap cases used by the
leaf induction.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB W ι : Type v}

/-- The A-support hypergraph carried by one embedded B-copy.  Its vertex
carrier is the full B-copy carrier; its hyperedges are precisely ambient
A-copies contained in that B-copy. -/
def bSupportPiece
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (b : Embedding B R) : HypergraphPiece W where
  carrier := copyCarrier b
  edges :=
    {e | ∃ a : Embedding A R,
      copyCarrier a = e ∧ copyCarrier a ⊆ copyCarrier b}
  edge_subset_carrier := by
    intro e he
    rcases he with ⟨a, ha, hsub⟩
    rw [← ha]
    exact hsub

/-- A join tree for B-support pieces is already a join tree for the full
B-copy carriers; the edge data play no role in running intersections. -/
def supportJoinTreeToBCopyJoinTree
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    {b : ι → Embedding B R}
    (J : JoinTree (fun i => bSupportPiece A (b i))) :
    BCopyJoinTree b where
  tree := J.tree
  isTree := J.isTree
  running := by
    intro x
    simpa [bSupportPiece, embeddingCarrierPiece] using J.running x

/-- Shared singleton intersections are supported inside both incident B-copies.
This is the exact relational hypothesis used after the support-forest geometry
has reduced an intersection to at most one vertex. -/
def PairwiseSharedVerticesSupported
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    (b : ι → Embedding B R) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ ⦃x : W⦄,
    x ∈ copyCarrier (b i) →
    x ∈ copyCarrier (b j) →
      VertexSupportedInBCopy A (b i) x ∧
        VertexSupportedInBCopy A (b j) x

/-- Pairwise allowed intersections of support hypergraphs, together with the
shared-support condition, are exactly the empty/A-copy/supported-point
trichotomy used by the relational induction. -/
theorem pairwiseSupportedBCopyOverlap_of_supportAllowed
    (A : RelStructure L UA)
    {B : RelStructure L VB} {R : RelStructure L W}
    {b : ι → Embedding B R}
    (hAllowed : PairwiseAllowed (fun i => bSupportPiece A (b i)))
    (hShared : PairwiseSharedVerticesSupported A b) :
    PairwiseSupportedBCopyOverlap A b := by
  intro i j hij
  rcases hAllowed hij with hSmall | hEdge
  · by_cases hEmpty :
        copyCarrier (b i) ∩ copyCarrier (b j) = ∅
    · exact Or.inl hEmpty
    · have hNonempty :
          (copyCarrier (b i) ∩ copyCarrier (b j)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hEmpty
      rcases hNonempty with ⟨x, hx⟩
      have hEq :
          copyCarrier (b i) ∩ copyCarrier (b j) = {x} := by
        apply Set.Subset.antisymm
        · intro y hy
          have hyx : y = x := hSmall hy hx
          simpa [hyx]
        · intro y hy
          have hyx : y = x := by simpa using hy
          simpa [hyx] using hx
      have hs := hShared hij hx.1 hx.2
      exact Or.inr (Or.inr ⟨x, hEq, hs.1, hs.2⟩)
  · rcases hEdge with ⟨e, heI, _heJ, hInter⟩
    change
      ∃ a : Embedding A R,
        copyCarrier a = e ∧
          copyCarrier a ⊆ copyCarrier (b i) at heI
    rcases heI with ⟨a, ha, _hsub⟩
    exact Or.inr (Or.inl ⟨a, hInter.trans ha.symm⟩)

/-- Hence every nonempty finite forest of B-support hypergraphs with supported
shared vertices embeds into an A-supported tree amalgam. -/
theorem supportForestOfBCopies_embeds_supportedTree
    {A : RelStructure L UA} {B : RelStructure L VB}
    {R : RelStructure L W}
    {b : ι → Embedding B R}
    [Fintype ι] [Nonempty ι]
    (hForest : ForestOfCopies (fun i => bSupportPiece A (b i)))
    (hShared : PairwiseSharedVerticesSupported A b)
    (alphaB : Embedding A B)
    (a0 a1 : UA) (hne : a0 ≠ a1) :
    ∃ (X : Type v) (T : RelStructure L X),
      ASupportedTreeAmalgam A B X T ∧
      Embedding (familyUnionStructure R b) T := by
  obtain ⟨J⟩ := hForest.joinTree_of_nonempty
  let JFull : BCopyJoinTree b :=
    supportJoinTreeToBCopyJoinTree A J
  have hOverlap :
      PairwiseSupportedBCopyOverlap A b :=
    pairwiseSupportedBCopyOverlap_of_supportAllowed
      A hForest.pairwiseAllowed hShared
  exact
    bCopyForest_embeds_supportedTree
      JFull hOverlap alphaB a0 a1 hne

end StructuralRamsey.Girth
