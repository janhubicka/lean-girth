import Girth.ContactJoinTreeCycles
import Girth.ContactZeroJoinTrees

/-! The two-member part of the mixed-forest property implies the
bottom G1 and G2 clauses. All copy and edge labels are kept distinct.
This does not assume the stronger bottom system-girth bound. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I E)


theorem zero_g1_of_pairwise (h0 : ∀ e, D.parent e = e)
    (hp : D.ZeroPairwise)
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i) :
    D.ContactG1 := by
  classical
  have hs : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial →
      e ∈ D.copyEdges i := by
    intro i e hn
    rcases hp (Sum.inr e) (Sum.inl i) (by intro he; cases he) with hs | ⟨f,hf,hfi,_⟩
    · obtain ⟨x,hx,y,hy,hxy⟩ := hn
      exact (hxy (hs hx hy)).elim
    · have he : f = e := hf
      subst f
      exact hfi
  refine ⟨hsub,hs,?_⟩
  intro i p htrigger x hx hxp
  have hxp' : x ∈ D.edgeCarrier p := by
    rw [← D.zero_wagonCarrier_eq h0]
    exact hxp
  have he : p ∈ D.copyEdges i := by
    rcases htrigger with hm | hn
    · obtain ⟨e,he,hpe⟩ := hm
      have h : e = p := (h0 e).symm.trans hpe
      subst e
      exact he
    · apply hs i p
      obtain ⟨u,hu,v,hv,huv⟩ := hn
      have huc : u ∈ D.edgeCarrier p := by
        rw [← D.zero_wagonCarrier_eq h0]
        exact hu.2
      have hvc : v ∈ D.edgeCarrier p := by
        rw [← D.zero_wagonCarrier_eq h0]
        exact hv.2
      exact ⟨u,⟨huc,hu.1⟩,v,⟨hvc,hv.1⟩,huv⟩
  exact ⟨p,he,h0 p,hxp'⟩

theorem zero_g2_of_pairwise (h0 : ∀ e, D.parent e = e)
    (hp : D.ZeroPairwise) (h1 : D.ContactG1)
    (hlin : D.ContactLinear) (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) :
    D.ContactG2 := by
  classical
  intro i j hij hn
  have hsupport : ∀ z : V ⊕ E, z ∈ D.contactCopyClique i →
      z ∈ D.contactCopyClique j →
      D.zeroContactSupport z ⊆ D.copyCarrier i ∩ D.copyCarrier j := by
    intro z hi hj x hx
    exact ⟨(D.zero_clique_support_iff h0 h1 hlin hsize (Sum.inl i) z).mp hi hx,
      (D.zero_clique_support_iff h0 h1 hlin hsize (Sum.inl j) z).mp hj hx⟩
  have hreal : (D.copyCarrier i ∩ D.copyCarrier j).Nontrivial := by
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    cases x with
    | inr p =>
      obtain ⟨u,hu,v,hv,huv⟩ := hsize p
      exact ⟨u,hsupport _ hx.1 hx.2 hu,v,hsupport _ hx.1 hx.2 hv,huv⟩
    | inl x =>
      cases y with
      | inr p =>
        obtain ⟨u,hu,v,hv,huv⟩ := hsize p
        exact ⟨u,hsupport _ hy.1 hy.2 hu,v,hsupport _ hy.1 hy.2 hv,huv⟩
      | inl y =>
        exact ⟨x,⟨hx.1,hx.2⟩,y,⟨hy.1,hy.2⟩,fun he => hxy (congrArg Sum.inl he)⟩
  rcases hp (Sum.inl i) (Sum.inl j) (fun he => hij (Sum.inl.inj he))
    with hs | ⟨e,_,_,he⟩
  · obtain ⟨x,hx,y,hy,hxy⟩ := hreal
    exact (hxy (hs hx hy)).elim
  · refine ⟨e,?_⟩
    intro z hz
    apply (D.zero_clique_support_iff h0 h1 hlin hsize (Sum.inr e) z).mpr
    have hh := hsupport z hz.1 hz.2
    change D.copyCarrier i ∩ D.copyCarrier j = D.edgeCarrier e at he
    change D.zeroContactSupport z ⊆ D.edgeCarrier e
    rw [← he]
    exact hh

theorem zero_edge_linearity_of_pairwise (hp : D.ZeroPairwise) :
    ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton := by
  intro e f hne
  rcases hp (Sum.inr e) (Sum.inr f) (fun he => hne (Sum.inr.inj he))
    with hs | ⟨g,he,hf,_⟩
  · exact hs
  · have hge : g = e := he
    have hgf : g = f := hf
    exact (hne (hge.symm.trans hgf)).elim

theorem zero_linearity_of_pairwise (h0 : ∀ e, D.parent e = e)
    (hp : D.ZeroPairwise) : D.ContactLinear := by
  refine ⟨D.zero_edge_linearity_of_pairwise hp,?_⟩
  intro e f hne
  rw [D.zero_wagonCarrier_eq h0,D.zero_wagonCarrier_eq h0]
  exact D.zero_edge_linearity_of_pairwise hp e f hne

end OrderOneData
end StructuralRamsey.Girth
