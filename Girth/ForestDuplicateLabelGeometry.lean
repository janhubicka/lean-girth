import Girth.ForestDuplicateLabelNormalization
import Girth.ForestJoinLiftLinear

/-!
# Duplicated owner labels are one-edge pieces in the linear ambient host

The exact manuscript join-tree lemma is SET-valued. The recursive
lift builds a forest on owner-labelled local completed members.
To pass from labels to the set of distinct physical pieces, one must
prove that a member duplicated under two labels is a ONE-EDGE
piece. This follows from ambient linearity, nonempty edge support
of every local member, and the outer allowed intersection.

No additional auxiliary uniqueness, vertex coverage or arbitrary
subforest heredity assumption is needed.

These are source-level candidate proofs awaiting Lean compilation.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- An edge-nonempty piece contained in an ambient support edge
must be exactly a one-edge piece when all ambient edges have size
at least two and the ambient family is linear.

No assumption that the piece is induced is needed. -/
theorem isOneEdge_of_linear_carrier_subset_edge
    (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hLarge : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (T : HypergraphPiece W)
    (hEdges : T.edges ⊆ H)
    (hNonempty : T.edges.Nonempty)
    (e : Set W) (he : e ∈ H)
    (hCarrier : T.carrier ⊆ e) :
    T.IsOneEdge := by
  classical
  have hEvery : ∀ f : Set W, f ∈ T.edges → f = e := by
    intro f hf
    by_contra hne
    have hBoth : (f ∩ e).Subsingleton :=
      hLinear (hEdges hf) he hne
    have hSub : f ⊆ e :=
      (T.edge_subset hf).trans hCarrier
    have hfSmall : f.Subsingleton := by
      intro x hx y hy
      exact hBoth ⟨hx, hSub hx⟩ ⟨hy, hSub hy⟩
    exact hLarge f (hEdges hf) hfSmall
  obtain ⟨f, hf⟩ := hNonempty
  have hCarrierEq : T.carrier = e := by
    apply Set.Subset.antisymm hCarrier
    rw [← hEvery f hf]
    exact T.edge_subset hf
  have hEdgesEq : T.edges = {e} := by
    ext g
    constructor
    · intro hg
      exact Set.mem_singleton_iff.mpr (hEvery g hg)
    · intro hg
      have hgEq : g = e := Set.mem_singleton_iff.mp hg
      rw [hgEq]
      have hfe : f = e := hEvery f hf
      simpa [hfe] using hf
  change T.edges = {T.carrier}
  rw [hEdgesEq, hCarrierEq]

/-- If different owner/member labels represent the same piece, it
is one-edge. This includes duplicate labels WITHIN a local forest
and duplicates across two different owners.

In the cross-owner case the common piece is contained in the whole
outer separator; linearity makes it exactly that edge. -/
theorem duplicatedLocalMember_isOneEdge_of_ambient_linear
    {K : Q → Type v}
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, PairwiseAllowed (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hLarge : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hOuterEdges :
      ∀ q : Q, (P q).edges ⊆ H)
    (hLocalEdges :
      ∀ q : Q, ∀ k : K q, (F q k).edges ⊆ H)
    (hLocalNonempty :
      ∀ q : Q, ∀ k : K q, (F q k).edges.Nonempty) :
    ∀ ⦃x y : Sigma K⦄,
      x ≠ y →
      F x.1 x.2 = F y.1 y.2 →
      (F x.1 x.2).IsOneEdge := by
  classical
  have hCarrierLarge :
      ∀ q : Q, ∀ k : K q,
        ¬(F q k).carrier.Subsingleton := by
    intro q k hSmall
    obtain ⟨f, hf⟩ := hLocalNonempty q k
    have hfSmall : f.Subsingleton := by
      intro x hx y hy
      exact hSmall ((F q k).edge_subset hf hx)
        ((F q k).edge_subset hf hy)
    exact hLarge f (hLocalEdges q k hf) hfSmall
  intro x y hne hEq
  rcases x with ⟨q, i⟩
  rcases y with ⟨r, j⟩
  by_cases hqr : q = r
  · subst r
    have hij : i ≠ j := by
      intro heq
      apply hne
      cases heq
      rfl
    rcases hLocal q hij with hSmall | ⟨e, heF, _heG, hIntersection⟩
    · have hCarSmall : (F q i).carrier.Subsingleton := by
        rw [← hEq] at hSmall
        simpa using hSmall
      exact (hCarrierLarge q i hCarSmall).elim
    · have hCarEq : (F q i).carrier = e := by
        rw [← hEq] at hIntersection
        simpa [Set.inter_self] using hIntersection
      apply isOneEdge_of_linear_carrier_subset_edge
        H hLinear hLarge (F q i) (hLocalEdges q i)
        (hLocalNonempty q i) e (hLocalEdges q i heF)
      rw [hCarEq]
      exact Set.Subset.rfl
  · have hCrossCarrier :
        (F q i).carrier ⊆
          (P q).carrier ∩ (P r).carrier := by
      intro z hz
      constructor
      · exact hContain q i hz
      · apply hContain r j
        rw [← hEq]
        exact hz
    rcases hOuter hqr with hSmall | ⟨e, heP, _heR, hOuterEq⟩
    · have hCarSmall : (F q i).carrier.Subsingleton := by
        intro x hx y hy
        exact hSmall (hCrossCarrier hx) (hCrossCarrier hy)
      exact (hCarrierLarge q i hCarSmall).elim
    · have hCarSubE : (F q i).carrier ⊆ e := by
        rw [← hOuterEq]
        exact hCrossCarrier
      exact isOneEdge_of_linear_carrier_subset_edge
        H hLinear hLarge (F q i) (hLocalEdges q i)
        (hLocalNonempty q i) e (hOuterEdges q heP)
        hCarSubE

/-- Fully SET-valued form of the general singleton-free lifting
lemma under the manuscript's ambient linearity and nonempty-edge
hypotheses. The only local requests are complete one-edge pieces
at separators with at least two vertices.

The conclusion is the forest on the DISTINCT physical pieces
of the local completed families. Request removal and identification
with the selected+designated family can be applied afterward. -/
theorem forestOfCopies_lift_local_without_singleton_on_set
    {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q : Q, Fintype (K q)]
    [∀ q : Q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocal : ∀ q : Q, ForestOfCopies (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (hEdgeRequest :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
        ∃ k : K q,
          F q k = HypergraphPiece.oneEdge
            ((P q).carrier ∩ (P r).carrier))
    (H : Set (Set W))
    (hLinear : LinearEdgeSet H)
    (hLarge : ∀ e : Set W, e ∈ H → ¬ e.Subsingleton)
    (hOuterEdges :
      ∀ q : Q, (P q).edges ⊆ H)
    (hLocalEdges :
      ∀ q : Q, ∀ k : K q, (F q k).edges ⊆ H)
    (hLocalNonempty :
      ∀ q : Q, ∀ k : K q, (F q k).edges.Nonempty) :
    ForestOfCopies
      (fun t : {t : HypergraphPiece W //
        t ∈ Finset.univ.image
          (fun z : Sigma K => F z.1 z.2)} => t.1) := by
  classical
  have hDuplicate :
      ∀ ⦃x y : Sigma K⦄, x ≠ y →
        F x.1 x.2 = F y.1 y.2 →
        (F x.1 x.2).IsOneEdge :=
    duplicatedLocalMember_isOneEdge_of_ambient_linear
      hOuter (fun q => (hLocal q).pairwiseAllowed)
      hContain H hLinear hLarge hOuterEdges hLocalEdges
      hLocalNonempty
  exact forestOfCopies_lift_without_singleton_on_distinct_image
    JOuter hLocal hContain hEdgeRequest hDuplicate

end StructuralRamsey.Girth
