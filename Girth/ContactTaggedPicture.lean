import Girth.ContactPictureData
import Girth.TrainWagonNodeGluing

/-! Actual tagged free-union construction at a single partition cut.

Use the same checked shared/private-node gluing for vertices, edges
and wagon classes. A shared edge has the common carrier and compatible
parent; an unshared edge belongs to its tagged standard copy.
The output vertex, edge and wagon types consist ONLY of generated
labels. This supplies the source maps used by ContactPictureData,
without assuming their geometric conclusions.

The ordered partite construction has to provide the partial gluing
maps on the active strip. No new Ramsey, linearity, or girth premise
is hidden in this construction. -/

namespace StructuralRamsey.Girth

universe v
variable {A B I : Type v}

/-- Generated (rather than all possible) tags of the free union. -/
def ContactGlued (g : I → B → Option A) :=
  {z : GluedWagonNode A B I g // z ∈ generatedWagonNodes g}

def contactCoreEmb (g : I → B → Option A) : A ↪ ContactGlued g where
  toFun a := ⟨gluedCoreNode g a,gluedCoreNode_generated g a⟩
  inj' := by
    intro a b he
    exact Sum.inl.inj (congrArg Subtype.val he)

def contactStandardEmb (g : I → B → Option A)
    (hinj : ∀ i b b' a, g i b = some a → g i b' = some a → b = b')
    (i : I) : B ↪ ContactGlued g where
  toFun b := ⟨gluedStandardNode g i b,gluedStandardNode_generated g i b⟩
  inj' := by
    intro b b' he
    exact gluedStandardNode_injective g hinj i (congrArg Subtype.val he)

theorem contactStandardEmb_eq_core (g : I → B → Option A)
    (hinj : ∀ i b b' a, g i b = some a → g i b' = some a → b = b')
    (i : I) (b : B) (a : A) :
    contactStandardEmb g hinj i b = contactCoreEmb g a ↔ g i b = some a := by
  constructor
  · intro he
    exact (gluedStandardNode_eq_core_iff g i b a).mp (congrArg Subtype.val he)
  · intro he
    exact Subtype.ext ((gluedStandardNode_eq_core_iff g i b a).mpr he)

theorem contactCoreEmb_mem_standard (g : I → B → Option A)
    (hinj : ∀ i b b' a, g i b = some a → g i b' = some a → b = b')
    (i : I) (a : A) :
    contactCoreEmb g a ∈ Set.range (contactStandardEmb g hinj i) ↔
      ∃ b, g i b = some a := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b,(contactStandardEmb_eq_core g hinj i b a).mp hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨b,(contactStandardEmb_eq_core g hinj i b a).mpr hb⟩

theorem contactGlued_cover (g : I → B → Option A)
    (hinj : ∀ i b b' a, g i b = some a → g i b' = some a → b = b')
    (z : ContactGlued g) : z ∈ Set.range (contactCoreEmb g) ∨
      ∃ i, z ∈ Set.range (contactStandardEmb g hinj i) := by
  rcases z.property with h | h
  · obtain ⟨a,ha⟩ := h
    exact Or.inl ⟨a,Subtype.ext ha⟩
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨b,hb⟩ := hi
    exact Or.inr ⟨i,b,Subtype.ext hb⟩

theorem contactGlued_shared (g : I → B → Option A)
    (hinj : ∀ i b b' a, g i b = some a → g i b' = some a → b = b')
    (i j : I) (hij : i ≠ j) (z : ContactGlued g)
    (hi : z ∈ Set.range (contactStandardEmb g hinj i))
    (hj : z ∈ Set.range (contactStandardEmb g hinj j)) :
    z ∈ Set.range (contactCoreEmb g) := by
  obtain ⟨b,hb⟩ := hi
  obtain ⟨b',hb'⟩ := hj
  obtain ⟨a,ha,_⟩ := gluedStandardNode_shared_of_distinct_indices
    g i j hij b b' (congrArg Subtype.val (hb.trans hb'.symm))
  exact ⟨a,((contactStandardEmb_eq_core g hinj i b a).mpr ha).symm.trans hb⟩

/-- The partial injections describing one active strip. The fields
about shared edge carriers and parent labels are precisely compatibility
of the train embeddings on the common strip. -/
structure ContactTaggedPicture {V E P V₀ E₀ I₀ P₀ : Type v}
    (D : OrderOneData V E I P) (L : OrderOneData V₀ E₀ I₀ P₀) where
  vertexGlue : I → V₀ → Option V
  edgeGlue : I → E₀ → Option E
  wagonGlue : I → P₀ → Option P
  vertex_inj : ∀ i x y a, vertexGlue i x = some a → vertexGlue i y = some a → x = y
  edge_inj : ∀ i e f a, edgeGlue i e = some a → edgeGlue i f = some a → e = f
  wagon_inj : ∀ i p q a, wagonGlue i p = some a → wagonGlue i q = some a → p = q
  vertex_domain : ∀ i x, (∃ y, vertexGlue i y = some x) ↔ x ∈ D.copyCarrier i
  edge_domain : ∀ i e, (∃ f, edgeGlue i f = some e) ↔ e ∈ D.copyEdges i
  wagon_domain : ∀ i p, (∃ q, wagonGlue i q = some p) ↔ D.contactMeets i p
  shared_edge_carrier : ∀ i f e, edgeGlue i f = some e →
    (contactStandardEmb vertexGlue vertex_inj i) '' L.edgeCarrier f =
      (contactCoreEmb vertexGlue) '' D.edgeCarrier e
  shared_parent : ∀ i f e, edgeGlue i f = some e →
    wagonGlue i (L.parent f) = some (D.parent e)
  core_parent_surj : Function.Surjective D.parent
  old_parent_surj : Function.Surjective L.parent

namespace ContactTaggedPicture

variable {V E P V₀ E₀ I₀ P₀ : Type v}
    {D : OrderOneData V E I P} {L : OrderOneData V₀ E₀ I₀ P₀}
    (T : ContactTaggedPicture D L)

abbrev Vertex := ContactGlued T.vertexGlue
abbrev Edge := ContactGlued T.edgeGlue
abbrev Wagon := ContactGlued T.wagonGlue

def coreV : V ↪ T.Vertex := contactCoreEmb T.vertexGlue
def coreE : E ↪ T.Edge := contactCoreEmb T.edgeGlue
def coreW : P ↪ T.Wagon := contactCoreEmb T.wagonGlue
def stdV (i : I) : V₀ ↪ T.Vertex := contactStandardEmb T.vertexGlue T.vertex_inj i
def stdE (i : I) : E₀ ↪ T.Edge := contactStandardEmb T.edgeGlue T.edge_inj i
def stdW (i : I) : P₀ ↪ T.Wagon := contactStandardEmb T.wagonGlue T.wagon_inj i

def outputCarrier (e : T.Edge) : Set T.Vertex :=
  match e.val with
  | .inl f => T.coreV '' D.edgeCarrier f
  | .inr (i,f) => (T.stdV i) '' L.edgeCarrier f

def outputParent (e : T.Edge) : T.Wagon :=
  match e.val with
  | .inl f => T.coreW (D.parent f)
  | .inr (i,f) => T.stdW i (L.parent f)

/-- Actual designated copies are lifted from the old picture,
indexed by the standard-copy index and the old copy index. -/
def output : OrderOneData T.Vertex T.Edge (I × I₀) T.Wagon where
  edgeCarrier := T.outputCarrier
  parent := T.outputParent
  copyCarrier := fun j => T.stdV j.1 '' L.copyCarrier j.2
  copyEdges := fun j => T.stdE j.1 '' L.copyEdges j.2

theorem output_carrier_core (e : E) :
    T.output.edgeCarrier (T.coreE e) = T.coreV '' D.edgeCarrier e := rfl

theorem output_parent_core (e : E) :
    T.output.parent (T.coreE e) = T.coreW (D.parent e) := rfl

theorem output_carrier_standard (i : I) (f : E₀) :
    T.output.edgeCarrier (T.stdE i f) = T.stdV i '' L.edgeCarrier f := by
  cases h : T.edgeGlue i f with
  | none =>
    change (match gluedStandardNode T.edgeGlue i f with
      | .inl e => T.coreV '' D.edgeCarrier e
      | .inr (j,e) => T.stdV j '' L.edgeCarrier e) =
        T.stdV i '' L.edgeCarrier f
    simp only [gluedStandardNode,h]
  | some e =>
    have he : T.stdE i f = T.coreE e :=
      (contactStandardEmb_eq_core T.edgeGlue T.edge_inj i f e).mpr h
    rw [he,T.output_carrier_core]
    exact (T.shared_edge_carrier i f e h).symm

theorem output_parent_standard (i : I) (f : E₀) :
    T.output.parent (T.stdE i f) = T.stdW i (L.parent f) := by
  cases h : T.edgeGlue i f with
  | none =>
    change (match gluedStandardNode T.edgeGlue i f with
      | .inl e => T.coreW (D.parent e)
      | .inr (j,e) => T.stdW j (L.parent e)) = T.stdW i (L.parent f)
    simp only [gluedStandardNode,h]
  | some e =>
    have he : T.stdE i f = T.coreE e :=
      (contactStandardEmb_eq_core T.edgeGlue T.edge_inj i f e).mpr h
    rw [he,T.output_parent_core]
    exact ((contactStandardEmb_eq_core T.wagonGlue T.wagon_inj
      i (L.parent f) (D.parent e)).mpr (T.shared_parent i f e h)).symm

theorem output_parent_surj : Function.Surjective T.output.parent := by
  intro r
  rcases contactGlued_cover T.wagonGlue T.wagon_inj r with ⟨p,rfl⟩ | ⟨i,p,rfl⟩
  · obtain ⟨e,he⟩ := T.core_parent_surj p
    exact ⟨T.coreE e,by rw [T.output_parent_core,he]⟩
  · obtain ⟨e,he⟩ := T.old_parent_surj p
    exact ⟨T.stdE i e,by rw [T.output_parent_standard,he]⟩

/-- The full actual one-level free-union picture data. Every map and
coverage field is supplied by the concrete tagged construction. -/
def toPictureData : ContactPictureData D L T.output where
  core := ⟨T.coreV,T.coreE,T.coreW,T.output_carrier_core,T.output_parent_core⟩
  std := fun i => ⟨T.stdV i,T.stdE i,T.stdW i,
    T.output_carrier_standard i,T.output_parent_standard i⟩
  vertex_cover := contactGlued_cover T.vertexGlue T.vertex_inj
  edge_cover := contactGlued_cover T.edgeGlue T.edge_inj
  parent_surjective := T.output_parent_surj
  std_core_vertex := fun i x =>
    (contactCoreEmb_mem_standard T.vertexGlue T.vertex_inj i x).trans (T.vertex_domain i x)
  std_core_edge := fun i e =>
    (contactCoreEmb_mem_standard T.edgeGlue T.edge_inj i e).trans (T.edge_domain i e)
  std_core_wagon := fun i p =>
    (contactCoreEmb_mem_standard T.wagonGlue T.wagon_inj i p).trans (T.wagon_domain i p)
  shared_vertex := contactGlued_shared T.vertexGlue T.vertex_inj
  shared_wagon := contactGlued_shared T.wagonGlue T.wagon_inj

/-- Wagon linearity in the ACTUAL tagged free union, not a record of
unconstructed output geometry. The gluing-map compatibility conditions
are the ordinary input conditions of the free amalgam. -/
theorem output_wagon_linearity (hD : D.ContactLinear)
    (h1 : D.ContactG1) (h2 : D.ContactG2) (h4 : ContactG4 D.contactClique 2)
    (hL : L.ContactLinear) :
    ∀ r s : T.Wagon, r ≠ s →
      (T.output.contactWagonCarrier r ∩ T.output.contactWagonCarrier s).Subsingleton :=
  T.toPictureData.wagon_linearity hD h1 h2 h4 hL

end ContactTaggedPicture
end StructuralRamsey.Girth
