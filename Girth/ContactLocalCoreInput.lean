import Girth.ContactPartPreservation

/-! The actual active strip, expressed in the fixed original part type.
For forest boost the part type and the parameter vector stay fixed across
recursive calls. A base edge gives a bijection between its vertices and
those parts; the witness is transported back by the inverse bijection.
No assumption about the next picture is introduced. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B L : Type v} {m : ℕ}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
variable {base : B → Set X} [LinearOrder V] [LinearOrder X] [LinearOrder L]

section SeedRelabelling
variable {a : ℕ} (label : X → L) (word : Fin a ≃o L)
    (enumeration : B → Fin a ↪o X)
    (he : ∀ b, base b = Set.range (enumeration b))
    (hw : ∀ b i, label (enumeration b i) = word i)

/-- On a base edge, the original labels give a bijection, since each
original part occurs exactly once in the common edge word. -/
theorem contact_seedLabel_bijective (b : B) :
    Function.Bijective (fun x : base b => label x.val) := by
  constructor
  · intro x y hxy
    have hx : x.val ∈ Set.range (enumeration b) := he b ▸ x.property
    have hy : y.val ∈ Set.range (enumeration b) := he b ▸ y.property
    obtain ⟨i,hi⟩ := hx
    obtain ⟨j,hj⟩ := hy
    have h : word i = word j := by rw [← hw b i,← hw b j,hi,hj]; exact hxy
    exact Subtype.ext (hi.symm.trans ((congrArg (enumeration b) (word.injective h)).trans hj))
  · intro i
    let j := word.symm i
    refine ⟨⟨enumeration b j,?_⟩,?_⟩
    · rw [he]; exact ⟨j,rfl⟩
    · rw [hw]; exact word.apply_symm_apply i

/-- This is the actual identification used in the class-wide forest
boost, not a new choice of labels for each vertex. -/
noncomputable def contact_seedLabelEquiv (b : B) : base b ≃ L :=
  Equiv.ofBijective (fun x : base b => label x.val)
    (contact_seedLabel_bijective label word enumeration he hw b)

/-- It is increasing on the base edge, even if the global seed order
is not concatenated by the original parts. -/
theorem contact_seedLabelEquiv_mono (b : B) :
    Monotone (contact_seedLabelEquiv label word enumeration he hw b) := by
  intro x y hxy
  have hx : x.val ∈ Set.range (enumeration b) := he b ▸ x.property
  have hy : y.val ∈ Set.range (enumeration b) := he b ▸ y.property
  obtain ⟨i,hi⟩ := hx
  obtain ⟨j,hj⟩ := hy
  have h : i ≤ j := by
    by_contra hn
    have hh := (enumeration b).strictMono (lt_of_not_ge hn)
    rw [hi,hj] at hh
    exact (not_lt_of_ge (show x.val ≤ y.val from hxy)) hh
  change label x.val ≤ label y.val
  rw [← hi,← hj,hw,hw]
  exact word.monotone h

/-- Pullback parameter sets agree on each base edge by definition. -/
theorem contact_seedLabelEquiv_parameter (b : B) (A : Set L) (x : base b) :
    x.val ∈ label ⁻¹' A ↔
      contact_seedLabelEquiv label word enumeration he hw b x ∈ A := Iff.rfl

end SeedRelabelling

namespace ContactBaseProjection
variable {H : ContactHypergraphData V E I} (P : ContactBaseProjection H base)

/-- The part map on an active strip, in a fixed type of original parts. -/
noncomputable def relabelStripEndpoints (b : B) (r : base b ≃ L) :
    ContactPartiteEndpoints (P.stripHypergraph b) L where
  part := fun x => r ((P.stripEndpoints b).part x)
  endpoint := fun e i => (P.stripEndpoints b).endpoint e (r.symm i)
  part_endpoint := by
    intro e i
    rw [(P.stripEndpoints b).part_endpoint,r.apply_symm_apply]
  carrier_eq := by
    intro e
    rw [(P.stripEndpoints b).carrier_eq]
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨r u,by simp⟩
    · rintro ⟨i,rfl⟩
      exact ⟨r.symm i,rfl⟩
  covered := P.strip_covered b

/-- The inverse relabelling sends every original part back to the
actual base vertex. This is needed for the eventual gluing. -/
theorem relabelStripEndpoints_part (b : B) (r : base b ≃ L)
    (x : P.StripVertex b) :
    (r.symm ((P.relabelStripEndpoints b r).part x)).val = P.stripPart b x := by
  change (r.symm (r ((P.stripEndpoints b).part x))).val = _
  exact congrArg Subtype.val (r.symm_apply_apply _)

end ContactBaseProjection

namespace ContactTrainPicture
variable {allowed : Fin m → Set X} {q : Fin (m+1) → ℕ}
    (P : ContactTrainPicture D T base allowed q) (b : B)

/-- A strip inherits the original parameter sets exactly, provided the
base edge relabelling identifies their restrictions with the old labels. -/
theorem strip_original_parameters (r : base b ≃ L) (A : Fin m → Set L)
    (hr : ∀ j (x : base b), x.val ∈ allowed j ↔ r x ∈ A j) :
    (P.projection.stripHypergraph b).Parameters (P.projection.stripTrain P.train b)
      (fun j => (P.projection.relabelStripEndpoints b r).part ⁻¹' A j) := by
  intro j e f x he hx hy hn
  have hn' : P.projection.vertex x.val ∉ allowed j := by
    intro hx'
    apply hn
    exact (hr j ((P.projection.stripEndpoints b).part x)).mp hx'
  exact P.projection.strip_parameter P.train b j.castSucc j.succ
    (P.projection.vertex ⁻¹' allowed j) (P.parameters j) e f x he hx hy hn'

/-- The positive proper wagon bounds required of a recursive input
are inherited directly, without transporting any designated copies. -/
theorem strip_positive_wagonBounds (μ : Fin (m+1))
    (hp : 0 < μ.val) (ht : μ.val < m) :
    LabelledGirthGT ((P.projection.stripHypergraph b).atCut
      ((P.projection.stripTrain P.train b).parent μ)).contactWagonCarrier (q μ) :=
  P.projection.strip_wagon_girth P.train b μ (P.positive μ hp ht).g3

/-- The restriction of the current order to the edge-covered strip is
monotone in the original part order, when the base edge is relabelled
by an increasing bijection. No global monotonicity of the seed labels
is necessary. -/
theorem strip_original_order (r : base b ≃ L) (hr : Monotone r) :
    letI : LinearOrder P.Vertex := P.order
    Monotone (P.projection.relabelStripEndpoints b r).part := by
  letI : LinearOrder P.Vertex := P.order
  intro x y h
  rcases lt_or_eq_of_le h with hlt | heq
  · apply hr
    exact P.projection_order x.val y.val hlt
  · exact le_of_eq (congrArg (P.projection.relabelStripEndpoints b r).part heq)

/-- A positive-level witness in the fixed original part type, ready
for gluing. Its part map and endpoints are genuine carrier data. -/
structure LocalWitness (r : base b ≃ L) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  finiteC : Finite Copy
  graph : ContactHypergraphData Vertex Edge Copy
  train : ContactTrainData Edge m
  family : ContactDesignatedEmbeddings (P.projection.stripHypergraph b)
    (P.projection.stripTrain P.train b) graph train
  endpoints : ContactPartiteEndpoints graph L
  emb_part : ∀ i x, endpoints.part ((family.emb i).vertex x) =
    (P.projection.relabelStripEndpoints b r).part x
  order : LinearOrder Vertex
  emb_order : ∀ i (x y : P.projection.StripVertex b), P.order.lt x.val y.val →
    order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  linear : ∀ e f, e ≠ f → (graph.edgeCarrier e ∩ graph.edgeCarrier f).Subsingleton
  positive : graph.PositiveBounds train q

namespace LocalWitness
variable {P b} {r : base b ≃ L} (W : P.LocalWitness b r)

/-- Pull back the original labels to the actual base vertices. -/
def basePart (x : W.Vertex) : X := (r.symm (W.endpoints.part x)).val

 theorem basePart_emb (i : W.Copy) (x : P.projection.StripVertex b) :
    W.basePart ((W.family.emb i).vertex x) = P.projection.stripPart b x := by
  unfold basePart
  rw [W.emb_part]
  exact P.projection.relabelStripEndpoints_part b r x

 theorem basePart_image (e : W.Edge) :
    W.basePart '' W.graph.edgeCarrier e = base b := by
  ext x
  constructor
  · rintro ⟨y,_,rfl⟩
    exact (r.symm (W.endpoints.part y)).property
  · intro hx
    let i : L := r ⟨x,hx⟩
    refine ⟨W.endpoints.endpoint e i,W.endpoints.endpoint_mem e i,?_⟩
    unfold basePart
    rw [W.endpoints.part_endpoint]
    exact congrArg Subtype.val (r.symm_apply_apply ⟨x,hx⟩)

 theorem basePart_inj (e : W.Edge) : Set.InjOn W.basePart (W.graph.edgeCarrier e) := by
  intro x hx y hy he
  have h : W.endpoints.part x = W.endpoints.part y :=
    r.symm.injective (Subtype.ext he)
  calc
    x = W.endpoints.endpoint e (W.endpoints.part x) :=
      (W.endpoints.endpoint_of_mem e x hx).symm
    _ = W.endpoints.endpoint e (W.endpoints.part y) := congrArg (W.endpoints.endpoint e) h
    _ = y := W.endpoints.endpoint_of_mem e y hy

/-- Construct the actual core, with no conclusion about the next picture
among its hypotheses. The parameters use the same equivalence as the
recursive input. -/
def toCore (A : Fin m → Set L)
    (hr : ∀ j (x : base b), x.val ∈ allowed j ↔ r x ∈ A j)
    (hpar : W.graph.Parameters W.train (fun j => W.endpoints.part ⁻¹' A j)) :
    P.Core b where
  Vertex := W.Vertex
  Edge := W.Edge
  Copy := W.Copy
  finiteV := W.finiteV
  finiteE := W.finiteE
  finiteC := W.finiteC
  graph := W.graph
  train := W.train
  family := W.family
  part := W.basePart
  part_emb := W.basePart_emb
  edge_image := W.basePart_image
  edge_inj := W.basePart_inj
  order := W.order
  copy_order := W.emb_order
  linear := W.linear
  covered := W.endpoints.covered
  parameters := by
    intro j e f x he hx hy hn
    apply hpar j e f x he hx hy
    intro h
    apply hn
    exact (hr j (r.symm (W.endpoints.part x))).mpr (by simpa using h)
  positive := W.positive

/-- The core has genuine nontrivial edges whenever the part type has
at least two elements. This is used by full system-girth preservation. -/
theorem nontrivial_edges [Nontrivial L] (e : W.Edge) :
    (W.graph.edgeCarrier e).Nontrivial := by
  obtain ⟨i,j,hij⟩ := exists_pair_ne L
  exact ⟨W.endpoints.endpoint e i,W.endpoints.endpoint_mem e i,
    W.endpoints.endpoint e j,W.endpoints.endpoint_mem e j,
    fun he => hij (W.endpoints.endpoint_inj e he)⟩

end LocalWitness
end ContactTrainPicture
end StructuralRamsey.Girth
