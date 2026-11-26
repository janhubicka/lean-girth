import Girth.ContactTrainEmbedding
import Girth.ContactCopyRestriction

/-! Transport of local chosen components into a designated
Ramsey copy. This constructs the actual ContactCopyRestriction
record at every proper positive level. The selected output
hypergraph is the same at every cut. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J C : Type v}

/-- A component partition and a local choice in each component.
The only cut-dependent facts are disjointness of the wagons and
the two local incidence conditions of the copy-restriction lemma.
They will be provided by the padded component construction. -/
structure ContactLocalSelection {m : ℕ}
    (D : ContactHypergraphData V E I) (T : ContactTrainData E m) (C : Type v) where
  vertexOwner : V → C
  edgeOwner : E → C
  edge_owner : ∀ e x, x ∈ D.edgeCarrier e → vertexOwner x = edgeOwner e
  chosenV : C → Set V
  chosenE : C → Set E
  vertex_sub : ∀ c x, x ∈ chosenV c → vertexOwner x = c
  edge_sub : ∀ c e, e ∈ chosenE c → edgeOwner e = c
  edge_vertices : ∀ c e, e ∈ chosenE c → D.edgeCarrier e ⊆ chosenV c
  strong : ∀ c e, edgeOwner e = c →
    (D.edgeCarrier e ∩ chosenV c).Nontrivial → e ∈ chosenE c
  proper_owner : ∀ μ, 0 < μ.val → μ.val < m → ∀ e f,
    T.parent μ e = T.parent μ f → edgeOwner e = edgeOwner f
  incidence : ∀ μ, 0 < μ.val → μ.val < m → ∀ c e x,
    edgeOwner e = c → x ∈ D.edgeCarrier e → x ∈ chosenV c →
      ∃ f, f ∈ chosenE c ∧ T.parent μ f = T.parent μ e ∧ x ∈ D.edgeCarrier f
  intersection : ∀ μ, 0 < μ.val → μ.val < m → ∀ c e f x,
    edgeOwner e = c → edgeOwner f = c → T.parent μ e ≠ T.parent μ f →
    x ∈ D.edgeCarrier e → x ∈ D.edgeCarrier f → x ∈ chosenV c

namespace ContactLocalSelection
variable {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (A : ContactLocalSelection D T C)
    (M : ContactDesignatedEmbeddings D T H S)

def selected : ContactHypergraphData U F (J × C) where
  edgeCarrier := H.edgeCarrier
  copyCarrier := fun j => (M.emb j.1).vertex '' A.chosenV j.2
  copyEdges := fun j => (M.emb j.1).edge '' A.chosenE j.2

/-- The partition and local incidence facts produce the concrete
copy-restriction data on the actual ambient labels. -/
def atCut (μ : Fin (m+1)) (hpos : 0 < μ.val) (hproper : μ.val < m) :
    ContactCopyRestriction (H.atCut (S.parent μ)) (J × C) where
  parentCopy := Prod.fst
  componentVertices := fun j => (M.emb j.1).vertex '' {x | A.vertexOwner x = j.2}
  componentEdges := fun j => (M.emb j.1).edge '' {e | A.edgeOwner e = j.2}
  chosenVertices := (A.selected M).copyCarrier
  chosenEdges := (A.selected M).copyEdges
  component_vertex_sub := by
    intro j x hx
    rw [M.vertex_eq]
    obtain ⟨u,_,he⟩ := hx
    exact ⟨u,he⟩
  component_edge_sub := by
    intro j e he
    rw [M.edge_eq]
    obtain ⟨f,_,h⟩ := he
    exact ⟨f,h⟩
  component_edge_vertices := by
    rintro ⟨j,c⟩ e ⟨f,hf,rfl⟩ x hx
    change x ∈ H.edgeCarrier ((M.emb j).edge f) at hx
    rw [(M.emb j).carrier_eq] at hx
    obtain ⟨u,hu,he⟩ := hx
    exact ⟨u,(A.edge_owner f u hu).trans hf,he⟩
  vertex_cover := by
    intro j x hx
    change x ∈ H.copyCarrier j at hx
    rw [M.vertex_eq] at hx
    obtain ⟨u,hu⟩ := hx
    exact ⟨(j,A.vertexOwner u),rfl,u,rfl,hu⟩
  edge_cover := by
    intro j e he
    change e ∈ H.copyEdges j at he
    rw [M.edge_eq] at he
    obtain ⟨f,hf⟩ := he
    exact ⟨(j,A.edgeOwner f),rfl,f,rfl,hf⟩
  component_vertex_unique := by
    rintro ⟨j,c⟩ ⟨k,d⟩ he x ⟨u,hu,hx⟩ ⟨w,hw,hy⟩
    change j = k at he
    subst k
    have h := (M.emb j).vertex.injective (hx.trans hy.symm)
    exact Prod.ext rfl (hu.symm.trans ((congrArg A.vertexOwner h).trans hw))
  component_wagon_unique := by
    rintro ⟨j,c⟩ ⟨k,d⟩ he e f ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ hp
    change j = k at he
    subst k
    change S.parent μ ((M.emb j).edge a) = S.parent μ ((M.emb j).edge b) at hp
    have h := A.proper_owner μ hpos hproper a b ((M.emb j).rel_iff μ a b |>.mp hp)
    exact Prod.ext rfl (ha.symm.trans (h.trans hb))
  chosen_vertex_sub := by
    rintro ⟨j,c⟩ x ⟨u,hu,he⟩
    exact ⟨u,A.vertex_sub c u hu,he⟩
  chosen_edge_sub := by
    rintro ⟨j,c⟩ e ⟨f,hf,he⟩
    exact ⟨f,A.edge_sub c f hf,he⟩
  chosen_edge_vertices := by
    rintro ⟨j,c⟩ e ⟨f,hf,rfl⟩ x hx
    change x ∈ H.edgeCarrier ((M.emb j).edge f) at hx
    rw [(M.emb j).carrier_eq] at hx
    obtain ⟨u,hu,he⟩ := hx
    exact ⟨u,A.edge_vertices c f hf hu,he⟩
  chosen_strong := by
    rintro ⟨j,c⟩ e ⟨f,hf,rfl⟩ hn
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    obtain ⟨u,hu,he⟩ := hx.2
    obtain ⟨w,hw,hg⟩ := hy.2
    have hu' : u ∈ D.edgeCarrier f :=
      ((M.emb j).mem_edge_image f u).mp (he.symm ▸ hx.1)
    have hw' : w ∈ D.edgeCarrier f :=
      ((M.emb j).mem_edge_image f w).mp (hg.symm ▸ hy.1)
    have hne : u ≠ w := fun h =>
      hxy (he.symm.trans ((congrArg (M.emb j).vertex h).trans hg))
    exact ⟨f,A.strong c f hf ⟨u,⟨hu',hu⟩,w,⟨hw',hw⟩,hne⟩,rfl⟩
  chosen_incidence := by
    rintro ⟨j,c⟩ p x ⟨u,hu,rfl⟩ ⟨e,⟨f,hf,rfl⟩,hp,hx⟩
    have huf := ((M.emb j).mem_edge_image f u).mp hx
    obtain ⟨a,ha,hparent,hua⟩ := A.incidence μ hpos hproper c f u hf huf hu
    refine ⟨(M.emb j).edge a,⟨a,ha,rfl⟩,?_,?_⟩
    · change S.parent μ ((M.emb j).edge a) = p
      exact ((M.emb j).rel_iff μ a f).mpr hparent |>.trans hp
    · exact ((M.emb j).mem_edge_image a u).mpr hua
  wagon_intersection_chosen := by
    rintro ⟨j,c⟩ e f x ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ hp hx hy
    change x ∈ H.edgeCarrier ((M.emb j).edge a) at hx
    rw [(M.emb j).carrier_eq] at hx
    obtain ⟨u,hu,rfl⟩ := hx
    have hb' := ((M.emb j).mem_edge_image b u).mp hy
    have hne : T.parent μ a ≠ T.parent μ b :=
      fun he => hp (((M.emb j).rel_iff μ a b).mpr he)
    exact ⟨u,A.intersection μ hpos hproper c a b u ha hb hne hu hb',rfl⟩

theorem selected_atCut (μ : Fin (m+1)) (hpos : 0 < μ.val) (hproper : μ.val < m) :
    (A.atCut M μ hpos hproper).chosen = (A.selected M).atCut (S.parent μ) := rfl

/-- The selected family inherits every positive proper system
bound by the certified copy-restriction theorem. -/
theorem preserves_positiveBounds (q : Fin (m+1) → ℕ)
    (h : H.PositiveBounds S q) :
    (A.selected M).PositiveBounds S q := by
  intro μ hp hproper
  exact (A.atCut M μ hp hproper).preserves_systemGirth (h μ hp hproper)

end ContactLocalSelection
end StructuralRamsey.Girth
