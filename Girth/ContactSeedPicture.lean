import Girth.ContactPictureZero
import Girth.ContactTrainEmbedding
import Girth.ContactActualStrip

/-! Picture zero over an actual seed. The seed embeddings do
not have to preserve a train; the new disjoint copies are given
the target's train independently. Projection and the seed
colouring property are proved on the actual labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B J : Type v}

structure ContactSeed (D : ContactHypergraphData V E I) (base : B → Set X)
    (J : Type v) where
  vertex : J → V ↪ X
  edge : J → E ↪ B
  carrier_eq : ∀ j e, base (edge j e) = vertex j '' D.edgeCarrier e
  strong : ∀ j b, (base b ∩ Set.range (vertex j)).Nontrivial →
    b ∈ Set.range (edge j)

namespace ContactSeed
variable {D : ContactHypergraphData V E I} {base : B → Set X}
    (A : ContactSeed D base J)

/-- Projection of picture zero onto the fixed seed hypergraph.
The designated copies are transversal and their projected
images are strongly induced. -/
def initialProjection : ContactBaseProjection (D.disjointCopies J) base where
  vertex := fun x => A.vertex x.1 x.2
  edge := fun e => A.edge e.1 e.2
  edge_image := by
    rintro ⟨i,e⟩
    rw [A.carrier_eq i e]
    ext x
    constructor
    · rintro ⟨⟨j,y⟩,hy,he⟩
      change j = i ∧ y ∈ D.edgeCarrier e at hy
      obtain ⟨h,hy⟩ := hy
      subst j
      exact ⟨y,hy,he⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(i,y),⟨rfl,hy⟩,rfl⟩
  edge_inj := by
    rintro ⟨i,e⟩ ⟨j,x⟩ hx ⟨k,y⟩ hy he
    change j = i ∧ x ∈ D.edgeCarrier e at hx
    change k = i ∧ y ∈ D.edgeCarrier e at hy
    obtain ⟨rfl,_⟩ := hx
    obtain ⟨rfl,_⟩ := hy
    exact Prod.ext rfl ((A.vertex i).injective he)
  copy_inj := by
    rintro i ⟨j,x⟩ hx ⟨k,y⟩ hy he
    change j = i at hx
    change k = i at hy
    subst j
    subst k
    exact Prod.ext rfl ((A.vertex i).injective he)
  copy_edge_subset := by
    rintro i ⟨j,e⟩ he ⟨k,x⟩ hx
    exact hx.1.trans he
  copy_strong := by
    intro i b hn
    have h : (base b ∩ Set.range (A.vertex i)).Nontrivial := by
      obtain ⟨x,hx,y,hy,hne⟩ := hn
      have hx' : x ∈ Set.range (A.vertex i) := by
        obtain ⟨⟨j,z⟩,hj,he⟩ := hx.2
        change j = i at hj
        subst j
        exact ⟨z,he⟩
      have hy' : y ∈ Set.range (A.vertex i) := by
        obtain ⟨⟨j,z⟩,hj,he⟩ := hy.2
        change j = i at hj
        subst j
        exact ⟨z,he⟩
      exact ⟨x,⟨hx.1,hx'⟩,y,⟨hy.1,hy'⟩,hne⟩
    obtain ⟨e,he⟩ := A.strong i b h
    exact ⟨(i,e),rfl,he⟩

variable {m : ℕ} (T : ContactTrainData E m) (hm : 0 < m)

/-- Each original train is literally a component of the
disjoint initial picture. -/
def initialEmbedding (_A : ContactSeed D base J) (i : J) :
    ContactTrainEmbedding D T (D.disjointCopies J) (T.disjointTrain J hm) where
  vertex := ⟨Prod.mk i,fun _ _ h => congrArg Prod.snd h⟩
  edge := ⟨Prod.mk i,fun _ _ h => congrArg Prod.snd h⟩
  carrier_eq := by
    intro e
    ext x
    constructor
    · rintro ⟨hx₁,hx₂⟩
      exact ⟨x.2,hx₂,Prod.ext hx₁.symm rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨rfl,hx⟩
  rel_iff := by
    intro μ e f
    constructor
    · intro he
      have h := Quotient.exact he
      change μ.val = m ∨ i = i ∧ T.parent μ e = T.parent μ f at h
      rcases h with ht | ⟨_,h⟩
      · have hμ : μ = (⟨m,by omega⟩ : Fin (m+1)) := Fin.ext ht
        rw [hμ]
        exact T.top e f
      · exact h
    · intro he
      exact Quotient.sound (Or.inr ⟨rfl,he⟩)
  strong := by
    rintro ⟨j,e⟩ hn
    obtain ⟨x,hx,_,_,_⟩ := hn
    obtain ⟨y,hy⟩ := hx.2
    have hj : i = j := (congrArg Prod.fst hy).trans hx.1.1
    subst j
    exact ⟨e,rfl⟩

def initialFamily :
    ContactDesignatedEmbeddings D T (D.disjointCopies J) (T.disjointTrain J hm) where
  emb := A.initialEmbedding T hm
  vertex_eq := by
    intro i
    ext x
    constructor
    · intro hx
      exact ⟨x.2,Prod.ext hx.symm rfl⟩
    · rintro ⟨x,rfl⟩
      rfl
  edge_eq := by
    intro i
    ext e
    constructor
    · intro he
      exact ⟨e.2,Prod.ext he.symm rfl⟩
    · rintro ⟨e,rfl⟩
      rfl

/-- Every initial active strip is a matching: each seed
embedding has at most one edge above a fixed base edge. -/
theorem initial_strip_matching (b : B) :
    ∀ e f : (A.initialProjection).StripEdge b, e ≠ f →
      ((A.initialProjection.stripHypergraph b).edgeCarrier e ∩
        (A.initialProjection.stripHypergraph b).edgeCarrier f) = ∅ := by
  intro e f hne
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hi : e.val.1 = f.val.1 := hx.1.1.symm.trans hx.2.1
  rcases e with ⟨⟨i,e⟩,he⟩
  rcases f with ⟨⟨j,f⟩,hf⟩
  change i = j at hi
  subst j
  have hef : e = f := (A.edge i).injective (he.trans hf.symm)
  subst f
  exact hne rfl

/-- The seed arrow is precisely the projected initial-copy
arrow used in reverse colour focusing. -/
theorem initial_seed_arrow {Color : Type v}
    (h : ∀ ρ : B → Color, ∃ j : J, ∃ c : Color, ∀ e, ρ (A.edge j e) = c) :
    ∀ ρ : B → Color, ∃ j : J, ∃ c : Color, ∀ e,
      ρ (A.initialProjection.edge (((A.initialFamily T hm).emb j).edge e)) = c :=
  h

end ContactSeed
end StructuralRamsey.Girth
