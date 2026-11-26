import Girth.ContactCliqueRestriction

/-! Concrete copy restriction (manuscript thm:scattering).
A new index is a component of an old designated copy, with a chosen
strongly induced subcopy. Edges and wagons of the ambient pretrain
remain literally unchanged. -/

namespace StructuralRamsey.Girth

universe v
variable {V E I P J : Type v}

structure ContactCopyRestriction (D : OrderOneData V E I P) (J : Type v) where
  parentCopy : J → I
  componentVertices : J → Set V
  componentEdges : J → Set E
  chosenVertices : J → Set V
  chosenEdges : J → Set E
  component_vertex_sub : ∀ j, componentVertices j ⊆ D.copyCarrier (parentCopy j)
  component_edge_sub : ∀ j, componentEdges j ⊆ D.copyEdges (parentCopy j)
  component_edge_vertices : ∀ j e, e ∈ componentEdges j →
    D.edgeCarrier e ⊆ componentVertices j
  vertex_cover : ∀ i x, x ∈ D.copyCarrier i →
    ∃ j, parentCopy j = i ∧ x ∈ componentVertices j
  edge_cover : ∀ i e, e ∈ D.copyEdges i →
    ∃ j, parentCopy j = i ∧ e ∈ componentEdges j
  component_vertex_unique : ∀ j k, parentCopy j = parentCopy k →
    ∀ x, x ∈ componentVertices j → x ∈ componentVertices k → j = k
  component_wagon_unique : ∀ j k, parentCopy j = parentCopy k →
    ∀ e f, e ∈ componentEdges j → f ∈ componentEdges k →
      D.parent e = D.parent f → j = k
  chosen_vertex_sub : ∀ j, chosenVertices j ⊆ componentVertices j
  chosen_edge_sub : ∀ j, chosenEdges j ⊆ componentEdges j
  chosen_edge_vertices : ∀ j e, e ∈ chosenEdges j → D.edgeCarrier e ⊆ chosenVertices j
  chosen_strong : ∀ j e, e ∈ componentEdges j →
    (D.edgeCarrier e ∩ chosenVertices j).Nontrivial → e ∈ chosenEdges j
  chosen_incidence : ∀ j p x, x ∈ chosenVertices j →
    (∃ e, e ∈ componentEdges j ∧ D.parent e = p ∧ x ∈ D.edgeCarrier e) →
    ∃ e, e ∈ chosenEdges j ∧ D.parent e = p ∧ x ∈ D.edgeCarrier e
  wagon_intersection_chosen : ∀ j e f x,
    e ∈ componentEdges j → f ∈ componentEdges j → D.parent e ≠ D.parent f →
    x ∈ D.edgeCarrier e → x ∈ D.edgeCarrier f → x ∈ chosenVertices j

namespace ContactCopyRestriction
variable {D : OrderOneData V E I P} (A : ContactCopyRestriction D J)

def components : OrderOneData V E J P where
  edgeCarrier := D.edgeCarrier
  parent := D.parent
  copyCarrier := A.componentVertices
  copyEdges := A.componentEdges

def chosen : OrderOneData V E J P where
  edgeCarrier := D.edgeCarrier
  parent := D.parent
  copyCarrier := A.chosenVertices
  copyEdges := A.chosenEdges

theorem component_clique_sub (j : J) :
    A.components.contactCopyClique j ⊆ D.contactCopyClique (A.parentCopy j) := by
  intro z hz
  cases z with
  | inl x => exact A.component_vertex_sub j hz
  | inr p =>
    obtain ⟨e,he,hp⟩ := hz
    exact ⟨e,A.component_edge_sub j he,hp⟩

theorem chosen_clique_sub (j : J) :
    A.chosen.contactCopyClique j ⊆ A.components.contactCopyClique j := by
  intro z hz
  cases z with
  | inl x => exact A.chosen_vertex_sub j hz
  | inr p =>
    obtain ⟨e,he,hp⟩ := hz
    exact ⟨e,A.chosen_edge_sub j he,hp⟩

theorem component_clique_cover (i : I) (z : V ⊕ P) (hz : z ∈ D.contactCopyClique i) :
    ∃ j, A.parentCopy j = i ∧ z ∈ A.components.contactCopyClique j := by
  cases z with
  | inl x => exact A.vertex_cover i x hz
  | inr p =>
    obtain ⟨e,he,hp⟩ := hz
    obtain ⟨j,hj,hje⟩ := A.edge_cover i e he
    exact ⟨j,hj,e,hje,hp⟩

theorem component_clique_unique (j k : J) (hpar : A.parentCopy j = A.parentCopy k)
    (z : V ⊕ P) (hzj : z ∈ A.components.contactCopyClique j)
    (hzk : z ∈ A.components.contactCopyClique k) : j = k := by
  cases z with
  | inl x => exact A.component_vertex_unique j k hpar x hzj hzk
  | inr p =>
    obtain ⟨e,he,hp⟩ := hzj
    obtain ⟨f,hf,hq⟩ := hzk
    exact A.component_wagon_unique j k hpar e f he hf (hp.trans hq.symm)

/-- An old-copy edge through a component vertex belongs to that
component, by the actual edge partition and vertex disjointness. -/
theorem edge_in_component (j : J) (e : E) (x : V)
    (he : e ∈ D.copyEdges (A.parentCopy j))
    (hx : x ∈ A.componentVertices j) (hxe : x ∈ D.edgeCarrier e) :
    e ∈ A.componentEdges j := by
  obtain ⟨k,hk,hke⟩ := A.edge_cover (A.parentCopy j) e he
  have hjk := A.component_vertex_unique j k hk.symm x hx
    (A.component_edge_vertices k e hke hxe)
  simpa only [hjk] using hke

/-- A pair in an old copy and a wagon supplies a local incidence at
each real vertex of the pair, not just a contact adjacency. -/
theorem component_bridge_of_pair (h1 : D.ContactG1)
    (j : J) (p : P) (x : V) (z : V ⊕ P)
    (hx : x ∈ A.componentVertices j)
    (hz : z ∈ D.contactCopyClique (A.parentCopy j))
    (hneq : (Sum.inl x : V ⊕ P) ≠ z)
    (hxp : x ∈ D.contactWagonCarrier p) (hzp : z ∈ D.contactWagonClique p) :
    ∃ e, e ∈ A.componentEdges j ∧ D.parent e = p ∧ x ∈ D.edgeCarrier e := by
  have hxi := A.component_vertex_sub j hx
  have htrigger : D.contactMeets (A.parentCopy j) p ∨
      (D.copyCarrier (A.parentCopy j) ∩ D.contactWagonCarrier p).Nontrivial := by
    cases z with
    | inl y =>
      right
      exact ⟨x,⟨hxi,hxp⟩,y,⟨hz,hzp⟩,fun he => hneq (congrArg Sum.inl he)⟩
    | inr w =>
      have he : w = p := hzp
      subst w
      exact Or.inl hz
  obtain ⟨e,he,hpe,hxe⟩ := h1.bridge (A.parentCopy j) p htrigger x hxi hxp
  exact ⟨e,A.edge_in_component j e x he hx hxe,hpe,hxe⟩

theorem component_meets_of_pair (h1 : D.ContactG1)
    (j : J) (p : P) (x z : V ⊕ P)
    (hx : x ∈ A.components.contactCopyClique j)
    (hz : z ∈ D.contactCopyClique (A.parentCopy j))
    (hne : x ≠ z) (hxp : x ∈ D.contactWagonClique p)
    (hzp : z ∈ D.contactWagonClique p) :
    A.components.contactMeets j p := by
  cases x with
  | inr w =>
    have he : w = p := hxp
    subst w
    exact hx
  | inl u =>
    obtain ⟨e,he,hpe,_⟩ := A.component_bridge_of_pair h1 j p u z hx hz hne hxp hzp
    exact ⟨e,he,hpe⟩

/-- No edge witnessed by a wagon clique crosses the component
partition of one old designated copy. -/
theorem stable_pair_component (h1 : D.ContactG1)
    (j k : J) (hpar : A.parentCopy j = A.parentCopy k)
    (p : P) (x y : V ⊕ P) (hxy : x ≠ y)
    (hx : x ∈ A.components.contactCopyClique j)
    (hy : y ∈ A.components.contactCopyClique k)
    (hxp : x ∈ D.contactWagonClique p) (hyp : y ∈ D.contactWagonClique p) :
    j = k := by
  have hxold : x ∈ D.contactCopyClique (A.parentCopy k) := by
    rw [← hpar]
    exact A.component_clique_sub j hx
  have hyold : y ∈ D.contactCopyClique (A.parentCopy j) := by
    rw [hpar]
    exact A.component_clique_sub k hy
  obtain ⟨e,he,hpe⟩ := A.component_meets_of_pair h1 j p x y hx hyold hxy hxp hyp
  obtain ⟨f,hf,hpf⟩ := A.component_meets_of_pair h1 k p y x hy hxold hxy.symm hyp hxp
  exact A.component_wagon_unique j k hpar e f he hf (hpe.trans hpf.symm)

/-- A discarded contact point has all neighbours inside its component
in one wagon clique. This is exactly condition (ii) of copy restriction. -/
theorem omitted_stable_unique (h1 : D.ContactG1) (j : J)
    (x y z : V ⊕ P) (p p' : P)
    (hx : x ∈ A.components.contactCopyClique j) (hn : x ∉ A.chosen.contactCopyClique j)
    (hy : y ∈ A.components.contactCopyClique j) (hz : z ∈ A.components.contactCopyClique j)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hxp : x ∈ D.contactWagonClique p) (hyp : y ∈ D.contactWagonClique p)
    (hxp' : x ∈ D.contactWagonClique p') (hzp' : z ∈ D.contactWagonClique p') :
    p = p' := by
  cases x with
  | inr w =>
    exact (show w = p from hxp).symm.trans (show w = p' from hxp')
  | inl u =>
    by_contra hne
    obtain ⟨e,he,hpe,hue⟩ := A.component_bridge_of_pair h1 j p u y hx
      (A.component_clique_sub j hy) hxy hxp hyp
    obtain ⟨f,hf,hpf,huf⟩ := A.component_bridge_of_pair h1 j p' u z hx
      (A.component_clique_sub j hz) hxz hxp' hzp'
    exact hn (A.wagon_intersection_chosen j e f u he hf
      (fun heq => hne (hpe.symm.trans (heq.trans hpf))) hue huf)

def cliqueRestriction (h1 : D.ContactG1) (h2 : D.ContactG2) :
    ContactCliqueRestriction D.contactCopyClique D.contactWagonClique A.chosen.contactCopyClique where
  parent := A.parentCopy
  component := A.components.contactCopyClique
  component_sub := A.component_clique_sub
  component_cover := A.component_clique_cover
  component_unique := A.component_clique_unique
  retained_sub := A.chosen_clique_sub
  old_shared := by
    intro i i' hne x y hxy hxi hyi hxi' hyi'
    exact D.contact_shared_pair_in_wagon h2
      (a := Sum.inl i) (b := Sum.inl i')
      (fun he => hne (Sum.inl.inj he)) hxy hxi hyi hxi' hyi'
  stable_pair_component := A.stable_pair_component h1
  omitted_stable_unique := A.omitted_stable_unique h1

/-- The strongness and wagon incidence conditions survive restriction.
All required edges are constructed from the old bridge and partition. -/
theorem preserves_g1 (h1 : D.ContactG1) : A.chosen.ContactG1 := by
  refine ⟨A.chosen_edge_vertices,?_,?_⟩
  · intro j e hne
    obtain ⟨x,hx,y,hy,hxy⟩ := hne
    have he := h1.strong (A.parentCopy j) e
      ⟨x,⟨hx.1,A.component_vertex_sub j (A.chosen_vertex_sub j hx.2)⟩,
       y,⟨hy.1,A.component_vertex_sub j (A.chosen_vertex_sub j hy.2)⟩,hxy⟩
    exact A.chosen_strong j e
      (A.edge_in_component j e x he (A.chosen_vertex_sub j hx.2) hx.1) ⟨x,hx,y,hy,hxy⟩
  · intro j p htrigger x hx hxp
    have hxi := A.component_vertex_sub j (A.chosen_vertex_sub j hx)
    have ht : D.contactMeets (A.parentCopy j) p ∨
        (D.copyCarrier (A.parentCopy j) ∩ D.contactWagonCarrier p).Nontrivial := by
      rcases htrigger with hm | hn
      · left
        obtain ⟨e,he,hpe⟩ := hm
        exact ⟨e,A.component_edge_sub j (A.chosen_edge_sub j he),hpe⟩
      · right
        obtain ⟨u,hu,v,hv,huv⟩ := hn
        exact ⟨u,⟨A.component_vertex_sub j (A.chosen_vertex_sub j hu.1),hu.2⟩,
          v,⟨A.component_vertex_sub j (A.chosen_vertex_sub j hv.1),hv.2⟩,huv⟩
    obtain ⟨e,he,hpe,hxe⟩ := h1.bridge (A.parentCopy j) p ht x hxi hxp
    exact A.chosen_incidence j p x hx
      ⟨e,A.edge_in_component j e x he (A.chosen_vertex_sub j hx) hxe,hpe,hxe⟩

theorem preserves_g2 (h2 : D.ContactG2) : A.chosen.ContactG2 := by
  classical
  intro j k hjk hn
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  by_cases hpar : A.parentCopy j = A.parentCopy k
  · exact (hjk (A.component_clique_unique j k hpar x
      (A.chosen_clique_sub j hx.1) (A.chosen_clique_sub k hx.2))).elim
  · have oldPair : (D.contactCopyClique (A.parentCopy j) ∩
        D.contactCopyClique (A.parentCopy k)).Nontrivial :=
      ⟨x,⟨A.component_clique_sub j (A.chosen_clique_sub j hx.1),
          A.component_clique_sub k (A.chosen_clique_sub k hx.2)⟩,
       y,⟨A.component_clique_sub j (A.chosen_clique_sub j hy.1),
          A.component_clique_sub k (A.chosen_clique_sub k hy.2)⟩,hxy⟩
    obtain ⟨p,hp⟩ := h2 _ _ hpar oldPair
    exact ⟨p,fun z hz => hp ⟨A.component_clique_sub j (A.chosen_clique_sub j hz.1),
      A.component_clique_sub k (A.chosen_clique_sub k hz.2)⟩⟩

/-- The full copy-restriction lemma. There is no old acceptable-cycle
bound, no hypothetical split, and no additional output-girth assumption. -/
theorem preserves_systemGirth {q : ℕ} (h : D.ContactSystemGirthGT q) :
    A.chosen.ContactSystemGirthGT q := by
  refine ⟨h.linear,A.preserves_g1 h.g1,A.preserves_g2 h.g2,h.g3,?_⟩
  have hOld : contactFamily D.contactCopyClique D.contactWagonClique = D.contactClique := by
    funext a
    cases a <;> rfl
  have hNew : contactFamily A.chosen.contactCopyClique D.contactWagonClique =
      A.chosen.contactClique := by
    funext a
    cases a <;> rfl
  rw [← hNew]
  apply (A.cliqueRestriction h.g1 h.g2).preserves_g4
  rw [hOld]
  exact h.g4

end ContactCopyRestriction
end StructuralRamsey.Girth
