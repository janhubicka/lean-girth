import Girth.ForestDistinctBoundaryComplete

/-!
# Exact local forest of genuine one-edge pieces and singleton requests

In the covered pure-to-mixed reduction, the local requests that do not
include the whole owner are individual support edges plus edge-free
singleton separators.  This result proves foresthood directly from
the girth bound on the DISTINCT physical support edges.

We reuse the fully verified boundary-incidence join-tree construction
rather than treating the forest property as hereditary under arbitrary
subfamilies. Repeated one-edge labels and repeated singleton requests
are permitted; only the physical support edges must be distinct.
-/

namespace StructuralRamsey.Girth

universe v
variable {W I E : Type v}

/-- Exact permitted local members, independent of their occurrence labels:
either a singleton/empty carrier, or an actual one-edge member from the
listed support edges. No vertex-cover condition is required. -/
def ShortLocalRequest
    (selected : I → HypergraphPiece W)
    (edge : E → Set W) : Prop :=
  ∀ i : I,
    (selected i).carrier.Subsingleton ∨
      ∃ e : E, selected i = HypergraphPiece.oneEdge (edge e)

/-- Every short request admits a physical incidence port:
none for empty carrier, an edge port for an actual support edge, and
a point port for a singleton. This does not add a formal ambient edge
at any singleton. -/
theorem exists_port_of_shortLocalRequest
    (selected : I → HypergraphPiece W)
    (edge : E → Set W)
    (hShort : ShortLocalRequest selected edge) :
    ∃ port : I → Option (E ⊕ W),
      BoundaryPortExact selected Set.univ edge id port := by
  classical
  have hChoice (i : I) :
      ∃ p : Option (E ⊕ W),
        match p with
        | none => (selected i).carrier = ∅
        | some (.inl e) => (selected i).carrier = edge e
        | some (.inr x) => (selected i).carrier = {x} := by
    rcases hShort i with hSmall | ⟨e, he⟩
    · by_cases hNonempty : (selected i).carrier.Nonempty
      · obtain ⟨x, hx⟩ := hNonempty
        refine ⟨some (.inr x), ?_⟩
        ext y
        constructor
        · intro hy
          have hxy : y = x := hSmall hy hx
          simpa [hxy]
        · intro hy
          have hyx : y = x := by simpa using hy
          simpa [hyx] using hx
      · refine ⟨none, ?_⟩
        ext y
        constructor
        · intro hy
          exact (hNonempty ⟨y, hy⟩).elim
        · intro hy
          simp at hy
    · refine ⟨some (.inl e), ?_⟩
      simp [he, HypergraphPiece.oneEdge]
  let port (i : I) : Option (E ⊕ W) :=
    Classical.choose (hChoice i)
  refine ⟨port, ?_⟩
  intro i
  have h :
      (match port i with
      | none => (selected i).carrier = ∅
      | some (.inl e) => (selected i).carrier = edge e
      | some (.inr x) => (selected i).carrier = {x}) :=
    Classical.choose_spec (hChoice i)
  change
    (match port i with
    | none => (selected i).carrier ∩ Set.univ = ∅
    | some (.inl e) => (selected i).carrier ∩ Set.univ = edge e
    | some (.inr v) => (selected i).carrier ∩ Set.univ = {id v})
  simpa [id] using h

/-- The mixed local family of genuine edge requests and edge-free singleton
requests is a forest when its DISTINCT physical support edges have local
girth greater than m. The number of request labels can exceed m because
duplicates or singleton labels cannot create new incidence cycles. -/
theorem forest_shortLocalRequest_of_girthGT
    [Fintype W] [Fintype I] [Nonempty I] [Fintype E]
    (selected : I → HypergraphPiece W)
    (edge : E → Set W)
    (hShort : ShortLocalRequest selected edge)
    (hEdgeInj : Function.Injective edge)
    (m : ℕ) (hm : 2 ≤ m)
    (hCard : Fintype.card E ≤ m)
    (hGirth : GirthGT (Set.range edge) m) :
    ForestOfCopies selected := by
  classical
  let S : Set W := Set.univ
  let K : Set (Set W) := Set.range edge
  let vertex : W → W := id
  obtain ⟨port, hPort⟩ :=
    exists_port_of_shortLocalRequest selected edge hShort
  have hLinear : LinearEdgeSet K := by
    intro e f he hf hef
    exact pairwise_subsingleton_of_girthGT_two
      (girthGT_mono hGirth hm) he hf hef
  have hBoundary :
      ∀ i, SmallOrWholeEdgeBoundary K S (selected i) := by
    intro i
    rcases hShort i with hSmall | ⟨e, he⟩
    · left
      simpa [S] using hSmall
    · right
      refine ⟨edge e, ⟨e, rfl⟩, ?_, ?_⟩
      · simp [he, HypergraphPiece.oneEdge]
      · simp [he, S, HypergraphPiece.oneEdge]
  have hCross :
      ∀ ⦃i j : I⦄, i ≠ j →
        (selected i).carrier ∩ (selected j).carrier ⊆ S := by
    intro i j _
    exact Set.subset_univ _
  have hEdge : ∀ e : E, edge e ∈ K := by
    intro e
    exact ⟨e, rfl⟩
  have hEdgeSub : ∀ e : E, edge e ⊆ S := by
    intro e
    exact Set.subset_univ _
  have hVertexSub : ∀ v : W, vertex v ∈ S := by
    intro v
    simp [S, vertex]
  have hRepresented :
      ∀ x : W, x ∈ S →
        (∃ z : I ⊕ (E ⊕ W),
          x ∈ (augmentedBoundaryPieces selected edge vertex z).carrier) →
        ∃ v : W, vertex v = x := by
    intro x _ _
    exact ⟨x, rfl⟩
  exact selectedForest_of_distinctBoundary_localGirth
    selected S K edge vertex port m
    hEdgeInj (fun _ _ h => h)
    hCard hGirth hLinear hBoundary hCross
    hEdge hEdgeSub hVertexSub hPort hRepresented

end StructuralRamsey.Girth
