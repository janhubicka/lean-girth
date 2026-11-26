import Girth.ContactTaggedPicture
import Girth.TrainLevelsData

/-! The actual train data behind the single-cut contact construction.
A wagon is a label of an equivalence class of edges, never just its
vertex carrier. Real vertices, edges and designated copies are common
to all cuts. The hierarchy is described by surjective parent maps;
the existing EdgeTrainLevels is recovered by taking their kernels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ : Type v}

/-- The three carrier maps of a picture, independent of train levels. -/
structure ContactHypergraphData (V E I : Type v) where
  edgeCarrier : E → Set V
  copyCarrier : I → Set V
  copyEdges : I → Set E

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

def atCut {P : Type v} (parent : E → P) : OrderOneData V E I P where
  edgeCarrier := D.edgeCarrier
  copyCarrier := D.copyCarrier
  copyEdges := D.copyEdges
  parent := parent

end ContactHypergraphData

/-- A presentation of a nested train by actual surjective wagon
labels. Distinct equal-carrier wagons remain distinct labels. -/
structure ContactTrainData (E : Type v) (m : ℕ) where
  Wagon : Fin (m+1) → Type v
  parent : (μ : Fin (m+1)) → E → Wagon μ
  surj : ∀ μ, Function.Surjective (parent μ)
  nested : ∀ μ ν, μ ≤ ν → ∀ e f, parent μ e = parent μ f → parent ν e = parent ν f
  bottom : Function.Injective (parent ⟨0,by omega⟩)
  top : ∀ e f, parent ⟨m,by omega⟩ e = parent ⟨m,by omega⟩ f

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

/-- The literal nested equivalence relation on edges. -/
def toLevels : EdgeTrainLevels E m where
  rel := fun μ e f => T.parent μ e = T.parent μ f
  equivalent := fun _ => ⟨fun _ => rfl,fun h => h.symm,fun h h' => h.trans h'⟩
  nested := T.nested
  bottom := fun e f => ⟨fun h => T.bottom h,fun h => congrArg _ h⟩
  top := T.top

/-- Actual class labels are bijective to the old quotient API. -/
noncomputable def wagonEquiv (μ : Fin (m+1)) :
    Quotient (T.toLevels.wagonSetoid μ) ≃ T.Wagon μ := by
  let f : Quotient (T.toLevels.wagonSetoid μ) → T.Wagon μ :=
    fun q => Quotient.liftOn q (T.parent μ) (fun _ _ h => h)
  have hf : Function.Injective f := by
    intro a b h
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b => exact Quotient.sound h
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨e,he⟩ := T.surj μ p
    exact ⟨Quotient.mk _ e,he⟩
  exact Equiv.ofBijective f ⟨hf,hs⟩

theorem wagonEquiv_mk (μ : Fin (m+1)) (e : E) :
    T.wagonEquiv μ (Quotient.mk _ e) = T.parent μ e := rfl

end ContactTrainData

/-- Every old nested-equivalence train has the corresponding
surjective class-label presentation. -/
def EdgeTrainLevels.toContactTrain {m : ℕ} (T : EdgeTrainLevels E m) :
    ContactTrainData E m where
  Wagon := fun μ => Quotient (T.wagonSetoid μ)
  parent := fun μ e => Quotient.mk (T.wagonSetoid μ) e
  surj := by
    intro μ p
    induction p using Quotient.inductionOn with
    | h e => exact ⟨e,rfl⟩
  nested := fun μ ν h e f he => Quotient.sound (T.nested μ ν h e f (Quotient.exact he))
  bottom := by
    intro e f he
    exact (T.bottom e f).mp (Quotient.exact he)
  top := fun e f => Quotient.sound (T.top e f)

theorem EdgeTrainLevels.toContactTrain_rel {m : ℕ} (T : EdgeTrainLevels E m)
    (μ : Fin (m+1)) (e f : E) :
    (T.toContactTrain.toLevels).rel μ e f ↔ T.rel μ e f :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound h⟩

/-- The active-strip gluing is fixed on vertices and edges. Its
compatibility at each train level is ordinary preservation and
reflection of wagon equivalence on shared edges. -/
structure ContactTrainStrip {m : ℕ}
    (D : ContactHypergraphData V E I)
    (L : ContactHypergraphData V₀ E₀ I₀)
    (T : ContactTrainData E m) (S : ContactTrainData E₀ m) where
  vertexGlue : I → V₀ → Option V
  edgeGlue : I → E₀ → Option E
  vertex_inj : ∀ i x y a, vertexGlue i x = some a → vertexGlue i y = some a → x = y
  edge_inj : ∀ i e f a, edgeGlue i e = some a → edgeGlue i f = some a → e = f
  vertex_domain : ∀ i x, (∃ y, vertexGlue i y = some x) ↔ x ∈ D.copyCarrier i
  edge_domain : ∀ i e, (∃ f, edgeGlue i f = some e) ↔ e ∈ D.copyEdges i
  shared_edge_carrier : ∀ i f e, edgeGlue i f = some e →
    (contactStandardEmb vertexGlue vertex_inj i) '' L.edgeCarrier f =
      (contactCoreEmb vertexGlue) '' D.edgeCarrier e
  shared_rel : ∀ μ i f f' e e', edgeGlue i f = some e → edgeGlue i f' = some e' →
    (S.parent μ f = S.parent μ f' ↔ T.parent μ e = T.parent μ e')
  shared_nonempty : ∀ i, ∃ f e, edgeGlue i f = some e

namespace ContactTrainStrip
variable {m : ℕ}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

abbrev Vertex := ContactGlued A.vertexGlue
abbrev Edge := ContactGlued A.edgeGlue

def coreV : V ↪ A.Vertex := contactCoreEmb A.vertexGlue
def coreE : E ↪ A.Edge := contactCoreEmb A.edgeGlue
def stdV (i : I) : V₀ ↪ A.Vertex := contactStandardEmb A.vertexGlue A.vertex_inj i
def stdE (i : I) : E₀ ↪ A.Edge := contactStandardEmb A.edgeGlue A.edge_inj i

/-- The shared wagon pair is witnessed by a genuine shared edge. -/
def WagonLink (μ : Fin (m+1)) (i : I) (p : S.Wagon μ) (r : T.Wagon μ) : Prop :=
  ∃ f e, A.edgeGlue i f = some e ∧ S.parent μ f = p ∧ T.parent μ e = r

theorem wagonLink_unique (μ : Fin (m+1)) (i : I)
    (p : S.Wagon μ) {r r' : T.Wagon μ}
    (h : A.WagonLink μ i p r) (h' : A.WagonLink μ i p r') : r = r' := by
  obtain ⟨f,e,hf,hp,hr⟩ := h
  obtain ⟨f',e',hf',hp',hr'⟩ := h'
  exact hr.symm.trans (((A.shared_rel μ i f f' e e' hf hf').mp
    (hp.trans hp'.symm)).trans hr')

theorem wagonLink_injective (μ : Fin (m+1)) (i : I)
    (r : T.Wagon μ) {p p' : S.Wagon μ}
    (h : A.WagonLink μ i p r) (h' : A.WagonLink μ i p' r) : p = p' := by
  obtain ⟨f,e,hf,hp,hr⟩ := h
  obtain ⟨f',e',hf',hp',hr'⟩ := h'
  exact hp.symm.trans (((A.shared_rel μ i f f' e e' hf hf').mpr
    (hr.trans hr'.symm)).trans hp')

/-- Compute the partial wagon gluing from edge gluing, at each cut. -/
noncomputable def wagonGlue (μ : Fin (m+1)) (i : I) (p : S.Wagon μ) :
    Option (T.Wagon μ) := by
  classical
  exact if h : ∃ r, A.WagonLink μ i p r then some (Classical.choose h) else none

theorem wagonGlue_iff (μ : Fin (m+1)) (i : I) (p : S.Wagon μ) (r : T.Wagon μ) :
    A.wagonGlue μ i p = some r ↔ A.WagonLink μ i p r := by
  classical
  unfold wagonGlue
  split_ifs with h
  · have hw := Classical.choose_spec h
    constructor
    · intro he
      exact (Option.some.inj he) ▸ hw
    · intro he
      exact congrArg some (A.wagonLink_unique μ i p hw he)
  · constructor
    · intro he
      cases he
    · intro he
      exact (h ⟨r,he⟩).elim

theorem wagonGlue_inj (μ : Fin (m+1)) :
    ∀ i p p' r, A.wagonGlue μ i p = some r → A.wagonGlue μ i p' = some r → p = p' := by
  intro i p p' r h h'
  exact A.wagonLink_injective μ i r
    ((A.wagonGlue_iff μ i p r).mp h) ((A.wagonGlue_iff μ i p' r).mp h')

/-- All wagon-domain and parent compatibility fields of the
previously checked tagged picture are now consequences. -/
noncomputable def atCut (μ : Fin (m+1)) :
    ContactTaggedPicture (D.atCut (T.parent μ)) (L.atCut (S.parent μ)) where
  vertexGlue := A.vertexGlue
  edgeGlue := A.edgeGlue
  wagonGlue := A.wagonGlue μ
  vertex_inj := A.vertex_inj
  edge_inj := A.edge_inj
  wagon_inj := A.wagonGlue_inj μ
  vertex_domain := A.vertex_domain
  edge_domain := A.edge_domain
  shared_edge_carrier := A.shared_edge_carrier
  shared_parent := by
    intro i f e he
    exact (A.wagonGlue_iff μ i (S.parent μ f) (T.parent μ e)).mpr
      ⟨f,e,he,rfl,rfl⟩
  wagon_domain := by
    intro i r
    constructor
    · rintro ⟨p,hp⟩
      obtain ⟨f,e,hf,_,he⟩ := (A.wagonGlue_iff μ i p r).mp hp
      exact ⟨e,(A.edge_domain i e).mp ⟨f,hf⟩,he⟩
    · rintro ⟨e,he,hr⟩
      obtain ⟨f,hf⟩ := (A.edge_domain i e).mpr he
      exact ⟨S.parent μ f,(A.wagonGlue_iff μ i _ _).mpr ⟨f,e,hf,rfl,hr⟩⟩
  core_parent_surj := T.surj μ
  old_parent_surj := S.surj μ

/-- The actual generated picture has one hypergraph, independent
of the cut at which it is viewed. -/
noncomputable def outputHypergraph : ContactHypergraphData A.Vertex A.Edge (I × I₀) where
  edgeCarrier := fun e => match e.val with
    | .inl f => A.coreV '' D.edgeCarrier f
    | .inr (i,f) => A.stdV i '' L.edgeCarrier f
  copyCarrier := fun j => A.stdV j.1 '' L.copyCarrier j.2
  copyEdges := fun j => A.stdE j.1 '' L.copyEdges j.2

theorem cut_output_eq (μ : Fin (m+1)) :
    (A.atCut μ).output =
      A.outputHypergraph.atCut (A.atCut μ).output.parent := by
  unfold ContactTaggedPicture.output ContactHypergraphData.atCut outputHypergraph
  congr 1
  funext e
  cases e with
  | mk t ht => cases t <;> rfl

end ContactTrainStrip
end StructuralRamsey.Girth
