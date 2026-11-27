import Girth.ContactRefinedStripInput
import Girth.ContactOrderedSeedIteration

/-! Connect the actual ordered linear seed to picture zero, and extract
an ordered witness with the original part labels from a final picture.
The seed and final family use the very same vertex and edge embeddings.
No order extension, Ramsey arrow, or system-girth conclusion is assumed
by the extraction. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P : Type v} [LinearOrder V] [LinearOrder P]
variable {D : ContactHypergraphData V E I} {a : ℕ}

namespace ContactOrderedEdgeWord.LinearSeedResult
variable {A : ContactOrderedEdgeWord D P a} {Color : Type v}
    (S : A.LinearSeedResult Color)

/-- The seed needs no train structure: its actual strong embeddings
supply the entire initial projection. -/
def toSeed : ContactSeed D S.graph.edgeCarrier S.Copy where
  vertex := fun i => (S.emb i).vertex
  edge := fun i => (S.emb i).edge
  carrier_eq := fun i e => (S.emb i).carrier_eq e
  strong := fun i e => (S.emb i).strong e

variable {m : ℕ} (T : ContactTrainData E m)
    (allowed : Fin m → Set P) (q : Fin (m+1) → ℕ)

/-- Every original parameter is the pullback of the corresponding
seed-part parameter. -/
theorem seed_parameters
    (hp : D.Parameters T (fun j => A.part ⁻¹' allowed j)) (i : S.Copy) :
    D.Parameters T (fun j => S.toSeed.vertex i ⁻¹' (S.part ⁻¹' allowed j)) := by
  intro j e f x he hx hy hn
  apply hp j e f x he hx hy
  intro hx'
  apply hn
  change S.part ((S.emb i).vertex x) ∈ allowed j
  rw [S.emb_part]
  exact hx'

/-- Picture zero over the seed produced by the actual finite Ramsey
construction, with the original parameters pulled back from the seed. -/
noncomputable def trainPicture [Finite V] [Finite E] (hm : 0 < m)
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hp : D.Parameters T (fun j => A.part ⁻¹' allowed j)) :
    letI : LinearOrder S.Vertex := S.order
    ContactTrainPicture D T S.graph.edgeCarrier (fun j => S.part ⁻¹' allowed j) q := by
  letI : LinearOrder S.Vertex := S.order
  letI : Finite S.Copy := S.finiteC
  exact S.toSeed.initialPicture hm (fun j => S.part ⁻¹' allowed j) q
    (fun i _ _ h => S.emb_order i _ _ h) hcovered hlin hg (S.seed_parameters T allowed hp)

 theorem trainPicture_fullBounds [Finite V] [Finite E] (hm : 0 < m)
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hp : D.Parameters T (fun j => A.part ⁻¹' allowed j)) :
    letI : LinearOrder S.Vertex := S.order
    (S.trainPicture T allowed q hm hcovered hlin hg hp).FullBounds := by
  letI : LinearOrder S.Vertex := S.order
  letI : Finite S.Copy := S.finiteC
  exact S.toSeed.initialPicture_fullBounds hm (fun j => S.part ⁻¹' allowed j) q
    (fun i _ _ h => S.emb_order i _ _ h) hcovered hlin hg (S.seed_parameters T allowed hp)

 theorem trainPicture_arrow [Finite V] [Finite E] (hm : 0 < m)
    (hcovered : ∀ x, ∃ e, x ∈ D.edgeCarrier e)
    (hlin : ∀ μ, μ.val < m → (D.atCut (T.parent μ)).ContactLinear)
    (hg : D.WagonBounds T q)
    (hp : D.Parameters T (fun j => A.part ⁻¹' allowed j)) :
    letI : LinearOrder S.Vertex := S.order
    let Q := S.trainPicture T allowed q hm hcovered hlin hg hp
    ∀ ρ : S.Edge → Color, ∃ i : Q.Copy, ∃ c : Color,
      ∀ e : E, ρ (Q.projection.edge ((Q.family.emb i).edge e)) = c := by
  letI : LinearOrder S.Vertex := S.order
  letI : Finite S.Copy := S.finiteC
  exact S.arrow

end ContactOrderedEdgeWord.LinearSeedResult

namespace ContactTrainPicture
variable {m : ℕ} {T : ContactTrainData E m}
variable {X B : Type v} [LinearOrder X]
variable {base : B → Set X} {allowed : Fin m → Set X} {q : Fin (m+1) → ℕ}
    (Q : ContactTrainPicture D T base allowed q)

/-- The projection of an edge is bijective. The order on a picture
therefore preserves the order of the base edge, not just its labels. -/
theorem edge_projection_reflect_lt {e : Q.Edge} {x y : Q.Vertex}
    (hx : x ∈ Q.graph.edgeCarrier e) (hy : y ∈ Q.graph.edgeCarrier e)
    (h : Q.projection.vertex x < Q.projection.vertex y) : Q.order.lt x y := by
  letI : LinearOrder Q.Vertex := Q.order
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | he
  · exact (not_lt_of_ge (Q.projection_order y x hlt)) h
  · exact (lt_irrefl _) (he ▸ h)

/-- Every position of the base edge lifts through the actual
bijection over that edge. -/
theorem liftEnumeration_exists (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b)) (e : Q.Edge) (i : Fin a) :
    ∃ x, x ∈ Q.graph.edgeCarrier e ∧
      Q.projection.vertex x = enumeration (Q.projection.edge e) i := by
  have hm : enumeration (Q.projection.edge e) i ∈ base (Q.projection.edge e) := by
    rw [he]
    exact ⟨i,rfl⟩
  rw [← Q.projection.edge_image e] at hm
  exact hm

/-- Lift every increasing enumeration of a base edge through the
actual bijection over that edge. -/
noncomputable def liftEnumeration (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b)) (e : Q.Edge) :
    letI : LinearOrder Q.Vertex := Q.order
    Fin a ↪o Q.Vertex := by
  classical
  letI : LinearOrder Q.Vertex := Q.order
  let f (i : Fin a) := Classical.choose (Q.liftEnumeration_exists enumeration he e i)
  have hf (i : Fin a) : f i ∈ Q.graph.edgeCarrier e ∧
      Q.projection.vertex (f i) = enumeration (Q.projection.edge e) i :=
    Classical.choose_spec (Q.liftEnumeration_exists enumeration he e i)
  refine OrderEmbedding.ofStrictMono f ?_
  intro i j hij
  apply Q.edge_projection_reflect_lt (hf i).1 (hf j).1
  rw [(hf i).2,(hf j).2]
  exact (enumeration (Q.projection.edge e)).strictMono hij

theorem liftEnumeration_spec (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b)) (e : Q.Edge) (i : Fin a) :
    letI : LinearOrder Q.Vertex := Q.order
    (Q.liftEnumeration enumeration he e i) ∈ Q.graph.edgeCarrier e ∧
    Q.projection.vertex (Q.liftEnumeration enumeration he e i) =
      enumeration (Q.projection.edge e) i := by
  letI : LinearOrder Q.Vertex := Q.order
  change Classical.choose (Q.liftEnumeration_exists enumeration he e i) ∈ Q.graph.edgeCarrier e ∧
    Q.projection.vertex (Classical.choose (Q.liftEnumeration_exists enumeration he e i)) =
      enumeration (Q.projection.edge e) i
  exact Classical.choose_spec (Q.liftEnumeration_exists enumeration he e i)

 theorem liftEnumeration_carrier (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b)) (e : Q.Edge) :
    letI : LinearOrder Q.Vertex := Q.order
    Q.graph.edgeCarrier e = Set.range (Q.liftEnumeration enumeration he e) := by
  classical
  letI : LinearOrder Q.Vertex := Q.order
  ext x
  constructor
  · intro hx
    have hm : Q.projection.vertex x ∈ base (Q.projection.edge e) := by
      rw [← Q.projection.edge_image e]
      exact ⟨x,hx,rfl⟩
    rw [he] at hm
    obtain ⟨i,hi⟩ := hm
    have h := Q.liftEnumeration_spec enumeration he e i
    exact ⟨i,Q.projection.edge_inj e h.1 hx (h.2.trans hi)⟩
  · rintro ⟨i,rfl⟩
    exact (Q.liftEnumeration_spec enumeration he e i).1

/-- Read the original part labels on the output by composing the
projection with the seed's labels. Its edge word is unchanged. -/
noncomputable def projectedEdgeWord (part : X → P) (word : Fin a → P)
    (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b))
    (hw : ∀ b i, part (enumeration b i) = word i) :
    letI : LinearOrder Q.Vertex := Q.order
    ContactOrderedEdgeWord Q.graph P a := by
  letI : LinearOrder Q.Vertex := Q.order
  exact {
    part := part ∘ Q.projection.vertex
    word := word
    enumeration := Q.liftEnumeration enumeration he
    carrier_eq := Q.liftEnumeration_carrier enumeration he
    part_eq := by
      intro e i
      change part (Q.projection.vertex (Q.liftEnumeration enumeration he e i)) = word i
      rw [(Q.liftEnumeration_spec enumeration he e i).2]
      exact hw _ _ }

end ContactTrainPicture
end StructuralRamsey.Girth
