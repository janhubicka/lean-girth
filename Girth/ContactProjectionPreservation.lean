import Girth.ContactBaseProjection

/-! The linear-base projection is preserved by the actual tagged
picture. This makes the projection/absorption adapter reusable at
the next step of the partite iteration, rather than an input that
must be independently re-established at every step. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

namespace ContactTrainStrip
variable {m : ℕ} {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

/-- The core is a partite hypergraph over the active edge. Its
projection agrees with the old projection along the actual gluing. -/
structure CoreOver {base : B → Set X} (P : ContactBaseProjection L base) (b : B)
    (p : V → X) : Prop where
  vertex_compatible : ∀ i x y, A.vertexGlue i x = some y → p y = P.vertex x
  edge_image : ∀ e, p '' D.edgeCarrier e = base b
  edge_inj : ∀ e, Set.InjOn p (D.edgeCarrier e)

def outputProjectionVertex {base : B → Set X} (P : ContactBaseProjection L base)
    (p : V → X) (x : A.Vertex) : X :=
  match x.val with
  | .inl y => p y
  | .inr (_,y) => P.vertex y

def outputProjectionEdge {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (e : A.Edge) : B :=
  match e.val with
  | .inl _ => b
  | .inr (_,f) => P.edge f

theorem projection_vertex_core {base : B → Set X} (P : ContactBaseProjection L base)
    (p : V → X) (x : V) : A.outputProjectionVertex P p (A.coreV x) = p x := rfl

theorem projection_vertex_std {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (p : V → X) (h : A.CoreOver P b p) (i : I) (x : V₀) :
    A.outputProjectionVertex P p (A.stdV i x) = P.vertex x := by
  cases he : A.vertexGlue i x with
  | none =>
    change (match gluedStandardNode A.vertexGlue i x with
      | .inl y => p y
      | .inr (_,y) => P.vertex y) = P.vertex x
    simp only [gluedStandardNode,he]
  | some y =>
    have hEq := (contactStandardEmb_eq_core A.vertexGlue A.vertex_inj i x y).mpr he
    change A.stdV i x = A.coreV y at hEq
    rw [hEq,A.projection_vertex_core]
    exact h.vertex_compatible i x y he

theorem projection_edge_core {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (e : E) : A.outputProjectionEdge P b (A.coreE e) = b := rfl

theorem projection_edge_std {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (h : A.ActiveOver P b) (i : I) (f : E₀) :
    A.outputProjectionEdge P b (A.stdE i f) = P.edge f := by
  cases he : A.edgeGlue i f with
  | none =>
    change (match gluedStandardNode A.edgeGlue i f with
      | .inl _ => b
      | .inr (_,e) => P.edge e) = P.edge f
    simp only [gluedStandardNode,he]
  | some e =>
    rw [A.shared_edge_eq i f e he,A.projection_edge_core]
    exact ((h.edge_domain i f).mp ⟨e,he⟩).symm

theorem projection_std_image {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (p : V → X) (h : A.CoreOver P b p) (i : I) (C : Set V₀) :
    A.outputProjectionVertex P p '' (A.stdV i '' C) = P.vertex '' C := by
  rw [Set.image_image]
  have he : A.outputProjectionVertex P p ∘ A.stdV i = P.vertex := by
    funext x
    exact A.projection_vertex_std P b p h i x
  rw [he]

theorem projection_core_image {base : B → Set X} (P : ContactBaseProjection L base)
    (p : V → X) (C : Set V) :
    A.outputProjectionVertex P p '' (A.coreV '' C) = p '' C := by
  rw [Set.image_image]
  rfl

theorem projection_std_injOn {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (p : V → X) (h : A.CoreOver P b p) (i : I) (C : Set V₀)
    (hi : Set.InjOn P.vertex C) :
    Set.InjOn (A.outputProjectionVertex P p) (A.stdV i '' C) := by
  rintro u ⟨x,hx,rfl⟩ v ⟨y,hy,rfl⟩ he
  rw [A.projection_vertex_std P b p h,A.projection_vertex_std P b p h] at he
  exact congrArg (A.stdV i) (hi hx hy he)

theorem projection_core_injOn {base : B → Set X} (P : ContactBaseProjection L base)
    (p : V → X) (C : Set V) (hi : Set.InjOn p C) :
    Set.InjOn (A.outputProjectionVertex P p) (A.coreV '' C) := by
  rintro u ⟨x,hx,rfl⟩ v ⟨y,hy,rfl⟩ he
  exact congrArg A.coreV (hi hx hy he)

/-- The actual output again has a linear-base projection, with
transversal strongly induced projected designated copies. -/
def outputProjection {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (p : V → X) (hA : A.ActiveOver P b) (h : A.CoreOver P b p) :
    ContactBaseProjection A.outputHypergraph base where
  vertex := A.outputProjectionVertex P p
  edge := A.outputProjectionEdge P b
  edge_image := by
    intro e
    rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
    · change A.outputProjectionVertex P p '' A.outputHypergraph.edgeCarrier (A.coreE f) =
        base (A.outputProjectionEdge P b (A.coreE f))
      have he := A.bottomPicture.output_carrier_core f
      rw [A.bottomPicture_output_eq] at he
      rw [he,A.projection_core_image,A.projection_edge_core,h.edge_image]
    · change A.outputProjectionVertex P p '' A.outputHypergraph.edgeCarrier (A.stdE i f) =
        base (A.outputProjectionEdge P b (A.stdE i f))
      have he := A.bottomPicture.output_carrier_standard i f
      rw [A.bottomPicture_output_eq] at he
      rw [he,A.projection_std_image P b p h,A.projection_edge_std P b hA,P.edge_image]
  edge_inj := by
    intro e
    rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
    · change Set.InjOn (A.outputProjectionVertex P p) (A.outputHypergraph.edgeCarrier (A.coreE f))
      have he := A.bottomPicture.output_carrier_core f
      rw [A.bottomPicture_output_eq] at he
      rw [he]
      exact A.projection_core_injOn P p _ (h.edge_inj f)
    · change Set.InjOn (A.outputProjectionVertex P p) (A.outputHypergraph.edgeCarrier (A.stdE i f))
      have he := A.bottomPicture.output_carrier_standard i f
      rw [A.bottomPicture_output_eq] at he
      rw [he]
      exact A.projection_std_injOn P b p h i _ (P.edge_inj f)
  copy_inj := by
    rintro ⟨i,j⟩
    exact A.projection_std_injOn P b p h i _ (P.copy_inj j)
  copy_edge_subset := by
    rintro ⟨i,j⟩ e ⟨f,hf,rfl⟩
    have he := A.bottomPicture.output_carrier_standard i f
    rw [A.bottomPicture_output_eq] at he
    change A.outputHypergraph.edgeCarrier (A.stdE i f) ⊆ A.stdV i '' L.copyCarrier j
    rw [he]
    exact Set.image_mono (P.copy_edge_subset j f hf)
  copy_strong := by
    rintro ⟨i,j⟩ c hn
    change (base c ∩ A.outputProjectionVertex P p '' (A.stdV i '' L.copyCarrier j)).Nontrivial at hn
    rw [A.projection_std_image P b p h] at hn
    obtain ⟨f,hf,he⟩ := P.copy_strong j c hn
    refine ⟨A.stdE i f,⟨f,hf,rfl⟩,?_⟩
    rw [A.projection_edge_std P b hA]
    exact he

end ContactTrainStrip
end StructuralRamsey.Girth
