import Girth.ForestJoinLift
import Girth.ForestSingleEdge

/-! # Linear outer supports imply cross-owner allowed intersections

The generic join-tree lifting theorem assumes that local members belonging to
different outer owners already have allowed intersections.  In the manuscript
this is not an extra hypothesis: it follows from linearity of the outer support
hypergraph together with the one-edge separator members inserted along the
outer join tree.  This file formalizes that derivation.
-/

namespace StructuralRamsey.Girth

universe v
variable {W Q : Type v}

/-- All support edges occurring in the outer pieces come from one linear
hypergraph: two distinct such edges meet in at most one vertex. -/
def OuterEdgesLinear
    (P : Q → HypergraphPiece W) : Prop :=
  ∀ ⦃q r : Q⦄ ⦃e f : Set W⦄,
    e ∈ (P q).edges →
    f ∈ (P r).edges →
    e ≠ f →
      (e ∩ f).Subsingleton

/-- Along the unique tree path between two owners, every vertex common to the
two endpoint pieces belongs to the first neighbour of the path. -/
theorem JoinTree.mem_snd_of_mem_endpoints
    {P : Q → HypergraphPiece W}
    (J : JoinTree P)
    {q r : Q}
    (hne : q ≠ r)
    (p : J.tree.Walk q r)
    (hp : p.IsPath)
    {x : W}
    (hxq : x ∈ (P q).carrier)
    (hxr : x ∈ (P r).carrier) :
    x ∈ (P p.snd).carrier := by
  let occ : Set Q := {s | x ∈ (P s).carrier}
  let qOcc : occ := ⟨q, hxq⟩
  let rOcc : occ := ⟨r, hxr⟩
  obtain ⟨po, hpo⟩ := (J.running x qOcc rOcc).exists_isPath
  let incl :
      (J.tree.induce occ) →g J.tree :=
    { toFun := fun z => z.1
      map_rel' := by
        intro a b hab
        exact hab }
  have hincl : Function.Injective incl := by
    intro a b h
    exact Subtype.ext h
  have hmap :
      (po.map incl).IsPath :=
    hpo.map hincl
  have hpath :
      (⟨po.map incl, hmap⟩ : J.tree.Path q r) =
        ⟨p, hp⟩ :=
    J.isTree.isAcyclic.subsingleton_path q r |>.elim _ _
  have hwalk : po.map incl = p :=
    congrArg Subtype.val hpath
  have hsnd : po.snd.1 = p.snd := by
    have h := congrArg (fun w => w.getVert 1) hwalk
    rw [SimpleGraph.Walk.getVert_map] at h
    change (po.getVert 1).1 = p.getVert 1 at h
    change (po.getVert 1).1 = p.getVert 1
    exact h
  simpa [hsnd] using po.snd.2

/-- A non-singleton outer intersection determines the same support edge at the
first separator on the tree path. -/
theorem JoinTree.first_separator_edge_eq
    {P : Q → HypergraphPiece W}
    (J : JoinTree P)
    (hOuter : PairwiseAllowed P)
    (hLinear : OuterEdgesLinear P)
    {q r : Q}
    (hne : q ≠ r)
    {e : Set W}
    (heq : (P q).carrier ∩ (P r).carrier = e)
    (heqEdge : e ∈ (P q).edges)
    (hbig : ¬ e.Subsingleton)
    (p : J.tree.Walk q r)
    (hp : p.IsPath) :
    (P q).carrier ∩ (P p.snd).carrier = e := by
  have hpnon : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hne
  have hadj : J.tree.Adj q p.snd :=
    p.adj_snd hpnon
  have heSubS : e ⊆ (P p.snd).carrier := by
    intro x hx
    have hxqr : x ∈ (P q).carrier ∩ (P r).carrier := by
      rw [heq]
      exact hx
    exact
      J.mem_snd_of_mem_endpoints
        hne p hp hxqr.1 hxqr.2
  have hsepBig :
      ¬((P q).carrier ∩ (P p.snd).carrier).Subsingleton := by
    intro hs
    apply hbig
    intro x hx y hy
    apply hs
    · exact ⟨(by
        have hxqr : x ∈ (P q).carrier ∩ (P r).carrier := by
          rw [heq]
          exact hx
        exact hxqr.1), heSubS hx⟩
    · exact ⟨(by
        have hyqr : y ∈ (P q).carrier ∩ (P r).carrier := by
          rw [heq]
          exact hy
        exact hyqr.1), heSubS hy⟩
  rcases hOuter hadj.ne with hsmall | ⟨d, hdq, hds, hsep⟩
  · exact (hsepBig hsmall).elim
  · have hed : e = d := by
      by_contra hneED
      have hsub : (e ∩ d).Subsingleton :=
        hLinear heqEdge hdq hneED
      apply hbig
      intro x hx y hy
      apply hsub
      · constructor
        · exact hx
        · have hxSep :
              x ∈ (P q).carrier ∩ (P p.snd).carrier :=
            ⟨(by
              have hxqr : x ∈ (P q).carrier ∩ (P r).carrier := by
                rw [heq]
                exact hx
              exact hxqr.1), heSubS hx⟩
          rw [hsep] at hxSep
          exact hxSep
      · constructor
        · exact hy
        · have hySep :
              y ∈ (P q).carrier ∩ (P p.snd).carrier :=
            ⟨(by
              have hyqr : y ∈ (P q).carrier ∩ (P r).carrier := by
                rw [heq]
                exact hy
              exact hyqr.1), heSubS hy⟩
          rw [hsep] at hySep
          exact hySep
    rw [hsep, ← hed]

/-- If two local members from different owners meet in more than one vertex,
the outer common support edge belongs to the endpoint local member. -/
theorem localMember_contains_outer_edge
    {K : Q → Type v}
    {P : Q → HypergraphPiece W}
    (JOuter : JoinTree P)
    (hOuter : PairwiseAllowed P)
    (hLinear : OuterEdgesLinear P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocalAllowed : ∀ q : Q, PairwiseAllowed (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (connector : (q r : Q) → K q)
    (hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier)
    (hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier)
    {q r : Q}
    (hne : q ≠ r)
    (i : K q) (j : K r)
    {e : Set W}
    (heq : (P q).carrier ∩ (P r).carrier = e)
    (heqEdge : e ∈ (P q).edges)
    (hbigLocal :
      ¬((F q i).carrier ∩ (F r j).carrier).Subsingleton) :
    e ∈ (F q i).edges := by
  classical
  obtain ⟨p, hp, _huniq⟩ := JOuter.isTree.existsUnique_path q r
  have hpnon : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hne
  have hadj : JOuter.tree.Adj q p.snd :=
    p.adj_snd hpnon
  have hbigE : ¬ e.Subsingleton := by
    intro hs
    apply hbigLocal
    intro x hx y hy
    apply hs
    · have hxOuter :
          x ∈ (P q).carrier ∩ (P r).carrier :=
        ⟨hContain q i hx.1, hContain r j hx.2⟩
      rw [heq] at hxOuter
      exact hxOuter
    · have hyOuter :
          y ∈ (P q).carrier ∩ (P r).carrier :=
        ⟨hContain q i hy.1, hContain r j hy.2⟩
      rw [heq] at hyOuter
      exact hyOuter
  have hsepEq :
      (P q).carrier ∩ (P p.snd).carrier = e :=
    JOuter.first_separator_edge_eq
      hOuter hLinear hne heq heqEdge hbigE p hp
  have hsepBig :
      ¬((P q).carrier ∩ (P p.snd).carrier).Subsingleton := by
    rw [hsepEq]
    exact hbigE
  obtain ⟨hOne, hConnCarrier⟩ :=
    hConnectorEdge hadj hsepBig
  have hConnCarrierE :
      (F q (connector q p.snd)).carrier = e := by
    rw [hConnCarrier, hsepEq]
  by_cases hic : i = connector q p.snd
  · subst i
    rw [hOne, hConnCarrierE]
    exact Set.mem_singleton e
  · have hLocal :=
      hLocalAllowed q hic
    have hLocalBig :
        ¬((F q i).carrier ∩
          (F q (connector q p.snd)).carrier).Subsingleton := by
      intro hs
      apply hbigLocal
      intro x hx y hy
      apply hs
      · refine ⟨hx.1, ?_⟩
        rw [hConnCarrierE, ← heq]
        exact ⟨hContain q i hx.1, hContain r j hx.2⟩
      · refine ⟨hy.1, ?_⟩
        rw [hConnCarrierE, ← heq]
        exact ⟨hContain q i hy.1, hContain r j hy.2⟩
    rcases hLocal with hsmall | ⟨d, hdi, hdconn, hinter⟩
    · exact (hLocalBig hsmall).elim
    · have hdEq : d = e := by
        have : d = (F q (connector q p.snd)).carrier := by
          rw [hOne] at hdconn
          simpa using hdconn
        exact this.trans hConnCarrierE
      simpa [hdEq] using hdi

/-- In the manuscript setup, linear outer support edges and the separator
members force all cross-owner local intersections to be allowed. -/
theorem crossAllowed_of_linear_outer
    {K : Q → Type v}
    {P : Q → HypergraphPiece W}
    (JOuter : JoinTree P)
    (hOuter : PairwiseAllowed P)
    (hLinear : OuterEdgesLinear P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocalAllowed : ∀ q : Q, PairwiseAllowed (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (connector : (q r : Q) → K q)
    (hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier)
    (hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier) :
    ∀ ⦃q r : Q⦄, q ≠ r →
      ∀ (i : K q) (j : K r),
        AllowedIntersection (F q i) (F r j) := by
  intro q r hne i j
  by_cases hsmall :
      ((F q i).carrier ∩ (F r j).carrier).Subsingleton
  · exact Or.inl hsmall
  · have hOuterBig :
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton := by
      intro hs
      apply hsmall
      intro x hx y hy
      apply hs
      · exact ⟨hContain q i hx.1, hContain r j hx.2⟩
      · exact ⟨hContain q i hy.1, hContain r j hy.2⟩
    rcases hOuter hne with hsmallOuter | ⟨e, heq, her, hinter⟩
    · exact (hOuterBig hsmallOuter).elim
    · have hei : e ∈ (F q i).edges :=
        localMember_contains_outer_edge
          JOuter hOuter hLinear hLocalAllowed hContain
          connector hConnector hConnectorEdge
          hne i j hinter heq hsmall
      have hej : e ∈ (F r j).edges := by
        have hinter' :
            (P r).carrier ∩ (P q).carrier = e := by
          simpa [Set.inter_comm] using hinter
        exact
          localMember_contains_outer_edge
            JOuter hOuter hLinear hLocalAllowed hContain
            connector hConnector hConnectorEdge
            hne.symm j i hinter' her
            (by simpa [Set.inter_comm] using hsmall)
      refine Or.inr ⟨e, hei, hej, ?_⟩
      apply Set.Subset.antisymm
      · intro x hx
        have hxOuter :
            x ∈ (P q).carrier ∩ (P r).carrier :=
          ⟨hContain q i hx.1, hContain r j hx.2⟩
        rw [hinter] at hxOuter
        exact hxOuter
      · intro x hx
        exact
          ⟨(F q i).edge_subset hei hx,
            (F r j).edge_subset hej hx⟩

/-- Exact linear-support wrapper around the generic outer join-tree lifting
theorem. -/
theorem forestOfCopies_lift_local_of_linear
    {K : Q → Type v}
    [Fintype Q] [Nonempty Q]
    [∀ q, Fintype (K q)] [∀ q, Nonempty (K q)]
    {P : Q → HypergraphPiece W}
    (hOuter : PairwiseAllowed P)
    (JOuter : JoinTree P)
    (hLinear : OuterEdgesLinear P)
    {F : (q : Q) → K q → HypergraphPiece W}
    (hLocalAllowed : ∀ q : Q, PairwiseAllowed (F q))
    (JLocal : ∀ q : Q, JoinTree (F q))
    (hContain :
      ∀ q (k : K q), (F q k).carrier ⊆ (P q).carrier)
    (connector : (q r : Q) → K q)
    (hConnector :
      ∀ ⦃q r : Q⦄, JOuter.tree.Adj q r →
        (P q).carrier ∩ (P r).carrier ⊆
          (F q (connector q r)).carrier)
    (hConnectorEdge :
      ∀ ⦃q r : Q⦄ (hadj : JOuter.tree.Adj q r),
        ¬((P q).carrier ∩ (P r).carrier).Subsingleton →
          (F q (connector q r)).IsOneEdge ∧
          (F q (connector q r)).carrier =
            (P q).carrier ∩ (P r).carrier) :
    ForestOfCopies (fun z : Sigma K => F z.1 z.2) :=
  forestOfCopies_lift_local
    hOuter JOuter hLocalAllowed JLocal hContain
    connector hConnector
    (crossAllowed_of_linear_outer
      JOuter hOuter hLinear hLocalAllowed hContain
      connector hConnector hConnectorEdge)

end StructuralRamsey.Girth
