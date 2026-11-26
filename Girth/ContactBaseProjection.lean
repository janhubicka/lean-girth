import Girth.ContactTrainBottom

/-! The projection/absorption calculation for a picture over a
linear base. This is the set-theoretic part of the ordered partite
adapter: the active strip is the inverse image of a base edge.
Transversal copies project injectively and strongly inducedly.
No forest or system-girth conclusion is an input. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v}

structure ContactBaseProjection (D : ContactHypergraphData V E I)
    (base : B → Set X) where
  vertex : V → X
  edge : E → B
  edge_image : ∀ e, vertex '' D.edgeCarrier e = base (edge e)
  edge_inj : ∀ e, Set.InjOn vertex (D.edgeCarrier e)
  copy_inj : ∀ i, Set.InjOn vertex (D.copyCarrier i)
  copy_edge_subset : ∀ i e, e ∈ D.copyEdges i → D.edgeCarrier e ⊆ D.copyCarrier i
  copy_strong : ∀ i b, (base b ∩ vertex '' D.copyCarrier i).Nontrivial →
    ∃ e, e ∈ D.copyEdges i ∧ edge e = b

namespace ContactBaseProjection
variable {D : ContactHypergraphData V E I} {base : B → Set X}
    (P : ContactBaseProjection D base)

def strip (b : B) : Set V := P.vertex ⁻¹' base b

theorem edge_subset_strip (e : E) (b : B) (he : P.edge e = b) :
    D.edgeCarrier e ⊆ P.strip b := by
  intro x hx
  change P.vertex x ∈ base b
  rw [← he,← P.edge_image]
  exact ⟨x,hx,rfl⟩

theorem edge_trace (hlin : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (e : E) (b : B) :
    (D.edgeCarrier e ∩ P.strip b).Subsingleton ∨
      P.edge e = b ∧ D.edgeCarrier e ∩ P.strip b = D.edgeCarrier e := by
  classical
  by_cases hs : (D.edgeCarrier e ∩ P.strip b).Subsingleton
  · exact Or.inl hs
  obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hs
  have hne : P.vertex x ≠ P.vertex y :=
    fun he => hxy (P.edge_inj e hx.1 hy.1 he)
  have hxb : P.vertex x ∈ base (P.edge e) := by
    rw [← P.edge_image]
    exact ⟨x,hx.1,rfl⟩
  have hyb : P.vertex y ∈ base (P.edge e) := by
    rw [← P.edge_image]
    exact ⟨y,hy.1,rfl⟩
  have he : P.edge e = b := by
    by_contra hn
    exact hne (hlin _ _ hn ⟨hxb,hx.2⟩ ⟨hyb,hy.2⟩)
  exact Or.inr ⟨he,Set.inter_eq_left.mpr (P.edge_subset_strip e b he)⟩

/-- A transversal designated copy has either a short trace or
exactly one of its own edges over the active base edge. -/
theorem copy_trace (i : I) (b : B) :
    (D.copyCarrier i ∩ P.strip b).Subsingleton ∨
      ∃ e, e ∈ D.copyEdges i ∧ P.edge e = b ∧
        D.copyCarrier i ∩ P.strip b = D.edgeCarrier e := by
  classical
  by_cases hs : (D.copyCarrier i ∩ P.strip b).Subsingleton
  · exact Or.inl hs
  obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hs
  have hne : P.vertex x ≠ P.vertex y :=
    fun he => hxy (P.copy_inj i hx.1 hy.1 he)
  obtain ⟨e,he,hb⟩ := P.copy_strong i b
    ⟨P.vertex x,⟨hx.2,⟨x,hx.1,rfl⟩⟩,
     P.vertex y,⟨hy.2,⟨y,hy.1,rfl⟩⟩,hne⟩
  refine Or.inr ⟨e,he,hb,Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    have hmem : P.vertex z ∈ P.vertex '' D.edgeCarrier e := by
      rw [P.edge_image,hb]
      exact hz.2
    obtain ⟨w,hw,hweq⟩ := hmem
    have hEq := P.copy_inj i (P.copy_edge_subset i e he hw) hz.1 hweq
    exact hEq ▸ hw
  · intro z hz
    exact ⟨P.copy_edge_subset i e he hz,P.edge_subset_strip e b hb hz⟩

theorem copy_absorption (i : I) (b : B) (e : E)
    (he : e ∈ D.copyEdges i) (hb : P.edge e = b) :
    D.copyCarrier i ∩ P.strip b = D.edgeCarrier e := by
  apply Set.Subset.antisymm
  · intro z hz
    have hmem : P.vertex z ∈ P.vertex '' D.edgeCarrier e := by
      rw [P.edge_image,hb]
      exact hz.2
    obtain ⟨w,hw,heq⟩ := hmem
    exact (P.copy_inj i (P.copy_edge_subset i e he hw) hz.1 heq) ▸ hw
  · intro z hz
    exact ⟨P.copy_edge_subset i e he hz,P.edge_subset_strip e b hb hz⟩

end ContactBaseProjection

namespace ContactTrainStrip
variable {U F J : Type v} {m : ℕ}
    {D : ContactHypergraphData U F J} {L : ContactHypergraphData V E I}
    {T : ContactTrainData F m} {S : ContactTrainData E m}
    (A : ContactTrainStrip D L T S)

/-- The active-strip data is the actual preimage of the base edge,
both on vertices and on edges, for every gluing. -/
structure ActiveOver {base : B → Set X} (P : ContactBaseProjection L base) (b : B) : Prop where
  vertex_domain : ∀ i x, (∃ y, A.vertexGlue i x = some y) ↔ x ∈ P.strip b
  edge_domain : ∀ i e, (∃ f, A.edgeGlue i e = some f) ↔ P.edge e = b

theorem stripStrong_of_projection {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hlin : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton) : A.StripStrong := by
  intro i e hn
  have he : L.edgeCarrier e ∩ {x | ∃ y, A.vertexGlue i x = some y} =
      L.edgeCarrier e ∩ P.strip b := by
    ext x
    exact and_congr_right (fun _ => hA.vertex_domain i x)
  rw [he] at hn
  rcases P.edge_trace hlin e b with hs | ⟨h,_⟩
  · obtain ⟨x,hx,y,hy,hxy⟩ := hn
    exact (hxy (hs hx hy)).elim
  · exact (hA.edge_domain i e).mpr h

theorem stripAbsorption_of_projection {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b) : A.StripAbsorption := by
  intro i j e he hshared x hx hxshared
  have hb := (hA.edge_domain i e).mp hshared
  have hs := P.copy_absorption j b e he hb
  have hmem : x ∈ L.copyCarrier j ∩ P.strip b := ⟨hx,(hA.vertex_domain i x).mp hxshared⟩
  rw [hs] at hmem
  exact hmem

/-- Exact edge trace with edge MEMBERSHIP, not merely carrier
equality. Both designated copies and edge copies are handled. -/
theorem stripTrace_of_projection {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hlin : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (i : J) (a : I ⊕ E) :
    ((L.bottomCut.carrier a) ∩ {x | ∃ y, A.vertexGlue i x = some y}).Subsingleton ∨
      ∃ e f, e ∈ L.bottomCut.edges a ∧ A.edgeGlue i e = some f ∧
        L.bottomCut.carrier a ∩ {x | ∃ y, A.vertexGlue i x = some y} =
          L.edgeCarrier e := by
  have hset : {x | ∃ y, A.vertexGlue i x = some y} = P.strip b := by
    ext x
    exact hA.vertex_domain i x
  rw [hset]
  cases a with
  | inl j =>
    rcases P.copy_trace j b with hs | ⟨e,he,hb,ht⟩
    · exact Or.inl hs
    · obtain ⟨f,hf⟩ := (hA.edge_domain i e).mpr hb
      exact Or.inr ⟨e,f,he,hf,ht⟩
  | inr e =>
    rcases P.edge_trace hlin e b with hs | ⟨hb,ht⟩
    · exact Or.inl hs
    · obtain ⟨f,hf⟩ := (hA.edge_domain i e).mpr hb
      exact Or.inr ⟨e,f,rfl,hf,ht⟩

end ContactTrainStrip
end StructuralRamsey.Girth
