import Girth.ContactTrainEmbedding
import Girth.ContactTrainBottom
import Girth.ContactZeroJoinTrees

/-! Remove repeated designated vertex images without changing the
underlying train. For strongly induced copies and edges of size
at least two, the vertex image determines the edge set. Retain
one actual representative per image. The contact graph, its
clique coverage and the wagon girth are unchanged; the pairwise
copy condition only becomes weaker. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P U F J : Type v}

namespace OrderOneData
variable (D : OrderOneData V E I P)

/-- A representative of each distinct vertex image. -/
abbrev ImageLabel := Set.range D.copyCarrier

noncomputable def imageRep (c : D.ImageLabel) : I :=
  Classical.choose c.property

theorem imageRep_carrier (c : D.ImageLabel) :
    D.copyCarrier (D.imageRep c) = c.val :=
  Classical.choose_spec c.property

theorem imageRep_injective : Function.Injective D.imageRep := by
  intro a b h
  apply Subtype.ext
  exact (D.imageRep_carrier a).symm.trans
    ((congrArg D.copyCarrier h).trans (D.imageRep_carrier b))

def imageLabel (i : I) : D.ImageLabel := ⟨D.copyCarrier i,⟨i,rfl⟩⟩

theorem imageLabel_surjective : Function.Surjective D.imageLabel := by
  intro c
  exact ⟨D.imageRep c,Subtype.ext (D.imageRep_carrier c)⟩

/-- If the old copy is strongly induced and its edge set is
contained in its vertex carrier, equal vertex images force
equal edge-label sets. -/
theorem sameImage_edges
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial → e ∈ D.copyEdges i)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    {i j : I} (he : D.copyCarrier i = D.copyCarrier j) :
    D.copyEdges i = D.copyEdges j := by
  ext e
  constructor
  · intro h
    apply hstrong j e
    obtain ⟨x,hx,y,hy,hne⟩ := hsize e
    exact ⟨x,⟨hx,he ▸ hsub i e h hx⟩,y,⟨hy,he ▸ hsub i e h hy⟩,hne⟩
  · intro h
    apply hstrong i e
    obtain ⟨x,hx,y,hy,hne⟩ := hsize e
    exact ⟨x,⟨hx,he.symm ▸ hsub j e h hx⟩,y,⟨hy,he.symm ▸ hsub j e h hy⟩,hne⟩

noncomputable def dedup : OrderOneData V E D.ImageLabel P where
  edgeCarrier := D.edgeCarrier
  parent := D.parent
  copyCarrier := fun c => c.val
  copyEdges := fun c => D.copyEdges (D.imageRep c)

/-- Every retained clique is exactly its old representative's
clique. -/
theorem dedup_clique (c : D.ImageLabel ⊕ P) :
    D.dedup.contactClique c =
      D.contactClique (c.map D.imageRep id) := by
  cases c with
  | inr p => rfl
  | inl i =>
    ext z
    cases z with
    | inl x =>
      change x ∈ i.val ↔ x ∈ D.copyCarrier (D.imageRep i)
      rw [D.imageRep_carrier]
    | inr p => rfl

/-- Every old clique survives as a set, even if its index was
not retained. -/
theorem dedup_all_cliques
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial → e ∈ D.copyEdges i)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial)
    (c : I ⊕ P) :
    D.dedup.contactClique (c.map D.imageLabel id) = D.contactClique c := by
  cases c with
  | inr p => rfl
  | inl i =>
    have he : D.copyCarrier (D.imageRep (D.imageLabel i)) = D.copyCarrier i :=
      D.imageRep_carrier (D.imageLabel i)
    have hE := D.sameImage_edges hsub hstrong hsize he
    ext z
    cases z with
    | inl x => rfl
    | inr p =>
      change (∃ e, e ∈ D.copyEdges (D.imageRep (D.imageLabel i)) ∧ D.parent e = p) ↔
        ∃ e, e ∈ D.copyEdges i ∧ D.parent e = p
      rw [hE]

theorem dedup_adj
    (hsub : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i)
    (hstrong : ∀ i e, (D.edgeCarrier e ∩ D.copyCarrier i).Nontrivial → e ∈ D.copyEdges i)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) (x y : V ⊕ P) :
    contactAdjacent D.dedup.contactClique x y ↔ contactAdjacent D.contactClique x y := by
  constructor
  · rintro ⟨hne,c,hx,hy⟩
    rw [D.dedup_clique c] at hx hy
    exact ⟨hne,c.map D.imageRep id,hx,hy⟩
  · rintro ⟨hne,c,hx,hy⟩
    exact ⟨hne,c.map D.imageLabel id,
      (D.dedup_all_cliques hsub hstrong hsize c).symm ▸ hx,
      (D.dedup_all_cliques hsub hstrong hsize c).symm ▸ hy⟩

/-- Deduplication preserves the full weighted contact-graph
system-girth invariant. In G4 both adjacency and covering
cliques survive; simply removing arbitrary copy labels would
not suffice for the covered-triangle clause. -/
theorem dedup_systemGirth {q : ℕ} (h : D.ContactSystemGirthGT q)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) :
    D.dedup.ContactSystemGirthGT q := by
  have hadj := D.dedup_adj h.g1.edge_subset h.g1.strong hsize
  refine ⟨h.linear,?_,?_,h.g3,?_⟩
  · constructor
    · intro i e he
      change D.edgeCarrier e ⊆ i.val
      rw [← D.imageRep_carrier i]
      exact h.g1.edge_subset (D.imageRep i) e he
    · intro i e he
      apply h.g1.strong (D.imageRep i) e
      rw [D.imageRep_carrier]
      exact he
    · intro i p ht x hx hp
      have ht' : D.contactMeets (D.imageRep i) p ∨
          (D.copyCarrier (D.imageRep i) ∩ D.contactWagonCarrier p).Nontrivial := by
        rw [D.imageRep_carrier]
        exact ht
      exact h.g1.bridge (D.imageRep i) p ht' x
        ((D.imageRep_carrier i).symm ▸ hx) hp
  · intro i j hij hn
    have hi := D.dedup_clique (Sum.inl i)
    have hj := D.dedup_clique (Sum.inl j)
    change D.dedup.contactCopyClique i = D.contactCopyClique (D.imageRep i) at hi
    change D.dedup.contactCopyClique j = D.contactCopyClique (D.imageRep j) at hj
    rw [hi,hj] at hn ⊢
    exact h.g2 _ _ (fun he => hij (D.imageRep_injective he)) hn
  · intro C hC hweight
    have hOld : C.IsCycle D.contactClique := fun i => (hadj _ _).mp (hC i)
    obtain ⟨htri,hchord⟩ := h.g4 C hOld hweight
    constructor
    · intro hlen
      obtain ⟨c,hc⟩ := htri hlen
      exact ⟨c.map D.imageLabel id,fun i =>
        (D.dedup_all_cliques h.g1.edge_subset h.g1.strong hsize c).symm ▸ hc i⟩
    · intro hlen
      obtain ⟨i,j,hij,he⟩ := hchord hlen
      exact ⟨i,j,hij,(hadj _ _).mpr he⟩

end OrderOneData

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

/-- The image labels and chosen representatives do not depend on
the cut. This is the same deduplicated family at every level. -/
abbrev ImageLabel := Set.range D.copyCarrier

noncomputable def imageRep (c : D.ImageLabel) : I :=
  Classical.choose c.property

noncomputable def dedup : ContactHypergraphData V E D.ImageLabel where
  edgeCarrier := D.edgeCarrier
  copyCarrier := fun c => c.val
  copyEdges := fun c => D.copyEdges (D.imageRep c)

theorem dedup_atCut (parent : E → P) :
    D.dedup.atCut parent = (D.atCut parent).dedup := rfl

theorem dedup_systemBounds {m : ℕ} (T : ContactTrainData E m)
    (q : Fin (m+1) → ℕ) (h : D.SystemBounds T q)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) :
    D.dedup.SystemBounds T q := by
  intro μ hproper
  rw [D.dedup_atCut]
  exact (D.atCut (T.parent μ)).dedup_systemGirth (h μ hproper) hsize

theorem dedup_positiveBounds {m : ℕ} (T : ContactTrainData E m)
    (q : Fin (m+1) → ℕ) (h : D.PositiveBounds T q)
    (hsize : ∀ e, (D.edgeCarrier e).Nontrivial) :
    D.dedup.PositiveBounds T q := by
  intro μ hp ht
  rw [D.dedup_atCut]
  exact (D.atCut (T.parent μ)).dedup_systemGirth (h μ hp ht) hsize

end ContactHypergraphData

namespace ContactDesignatedEmbeddings
variable {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactDesignatedEmbeddings D T H S)

noncomputable def dedup : ContactDesignatedEmbeddings D T H.dedup S where
  emb := fun c =>
    let f := M.emb (H.imageRep c)
    { vertex := f.vertex
      edge := f.edge
      carrier_eq := f.carrier_eq
      rel_iff := f.rel_iff
      strong := f.strong }
  vertex_eq := by
    intro c
    change c.val = Set.range (M.emb (H.imageRep c)).vertex
    rw [← M.vertex_eq]
    exact (Classical.choose_spec c.property).symm
  edge_eq := fun c => M.edge_eq (H.imageRep c)

/-- The representative of an image has the same edge set as
the original label, because the embeddings are strong. Thus
deduplicating the images cannot lose the Ramsey arrow. -/
theorem dedup_arrow {Color : Type v}
    (hsize : ∀ e, (H.edgeCarrier e).Nontrivial)
    (h : M.Arrow Color) : M.dedup.Arrow Color := by
  intro χ
  obtain ⟨j,c,hj⟩ := h χ
  let label : H.ImageLabel := ⟨H.copyCarrier j,⟨j,rfl⟩⟩
  refine ⟨label,c,?_⟩
  have hsub : ∀ i e, e ∈ H.copyEdges i → H.edgeCarrier e ⊆ H.copyCarrier i := by
    intro i e he
    rw [M.edge_eq] at he
    obtain ⟨f,rfl⟩ := he
    rw [M.vertex_eq]
    exact (M.emb i).vertex_range_of_edge f
  have hstrong : ∀ i e, (H.edgeCarrier e ∩ H.copyCarrier i).Nontrivial → e ∈ H.copyEdges i := by
    intro i e he
    rw [M.vertex_eq] at he
    rw [M.edge_eq]
    exact (M.emb i).strong e he
  have he : H.copyCarrier (H.imageRep label) = H.copyCarrier j :=
    Classical.choose_spec label.property
  have hE : H.copyEdges (H.imageRep label) = H.copyEdges j :=
    (H.bottomCut).sameImage_edges hsub hstrong hsize he
  intro e
  have hm : (M.emb (H.imageRep label)).edge e ∈ H.copyEdges (H.imageRep label) := by
    rw [M.edge_eq]
    exact ⟨e,rfl⟩
  rw [hE,M.edge_eq] at hm
  obtain ⟨f,hf⟩ := hm
  change χ ((M.emb (H.imageRep label)).edge e) = c
  rw [← hf]
  exact hj f

end ContactDesignatedEmbeddings
end StructuralRamsey.Girth
