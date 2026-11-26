import Girth.ContactNonlinearSeedStep
import Girth.ContactWordBase
import Girth.ContactSeedPicture

/-! The nonlinear seed stage need not store its designated
target copies in the train incidence data. Keep their actual
embeddings separately. The copy-free projection then satisfies
the existing ContactBaseProjection interface vacuously on
designated copies, so the same actual strip adapter applies. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I U F J X B : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

def noCopies : ContactHypergraphData V E PEmpty.{v+1} where
  edgeCarrier := D.edgeCarrier
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

end ContactHypergraphData

namespace ContactBaseProjection
variable {D : ContactHypergraphData V E I} {base : B → Set X}
    (P : ContactBaseProjection D base)

def noCopies : ContactBaseProjection D.noCopies base where
  vertex := P.vertex
  edge := P.edge
  edge_image := P.edge_image
  edge_inj := P.edge_inj
  copy_inj := PEmpty.elim
  copy_edge_subset := PEmpty.elim
  copy_strong := by intro i; cases i

end ContactBaseProjection

namespace ContactTrainEmbedding
variable {m : ℕ} {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
    {H : ContactHypergraphData U F J} {S : ContactTrainData F m}
    (M : ContactTrainEmbedding D T H S)

def noTargetCopies : ContactTrainEmbedding D T H.noCopies S where
  vertex := M.vertex
  edge := M.edge
  carrier_eq := M.carrier_eq
  rel_iff := M.rel_iff
  strong := M.strong

end ContactTrainEmbedding

/-- The height-one train, with bottom equality and universal
top. Its wagon labels are literal edges and a range of the
constant map, so even the empty edge family is permitted. -/
def contactHeightOne (E : Type v) : ContactTrainData E 1 :=
  let T : EdgeTrainLevels E 1 := {
    rel := fun μ e f => μ.val = 1 ∨ e = f
    equivalent := by
      intro μ
      refine ⟨fun _ => Or.inr rfl,?_,?_⟩
      · intro e f h
        exact h.elim Or.inl (fun he => Or.inr he.symm)
      · intro e f g h h'
        rcases h with h | h
        · exact Or.inl h
        · exact h' |>.elim Or.inl (fun he => Or.inr (h.trans he))
    nested := by
      intro μ ν h e f he
      rcases he with ht | he
      · left
        have hv : μ.val ≤ ν.val := h
        have hn := ν.isLt
        omega
      · exact Or.inr he
    bottom := by intro e f; simp
    top := fun _ _ => Or.inl rfl
  }
  T.toContactTrain

theorem contactHeightOne_rel (μ : Fin 2) (e f : E) :
    (contactHeightOne E).parent μ e = (contactHeightOne E).parent μ f ↔
      μ.val = 1 ∨ e = f :=
  ⟨fun he => Quotient.exact he,fun he => Quotient.sound he⟩

/-- Any injection between height-one edge types reflects both
train cuts. -/
theorem contactHeightOne_embedding_rel (f : E ↪ F) (μ : Fin 2) (e g : E) :
    (contactHeightOne F).parent μ (f e) = (contactHeightOne F).parent μ (f g) ↔
      (contactHeightOne E).parent μ e = (contactHeightOne E).parent μ g := by
  rw [contactHeightOne_rel,contactHeightOne_rel]
  exact or_congr Iff.rfl ⟨fun he => f.injective he,fun he => congrArg f he⟩

namespace ContactBaseProjection
variable {L : ContactHypergraphData V E I} {base : B → Set X}
    (P : ContactBaseProjection L base) (b : B)

theorem strip_endpoint_exists (e : P.StripEdge b) (a : base b) :
    ∃ x, x ∈ L.edgeCarrier e.val ∧ P.vertex x = a.val := by
  have h : (a.val : X) ∈ base (P.edge e.val) := by
    rw [e.property]
    exact a.property
  rw [← P.edge_image] at h
  exact h

noncomputable def stripEndpoint (e : P.StripEdge b) (a : base b) : P.StripVertex b :=
  ⟨Classical.choose (P.strip_endpoint_exists b e a),
    P.edge_subset_strip e.val b e.property (Classical.choose_spec (P.strip_endpoint_exists b e a)).1⟩

noncomputable def stripEndpoints :
    ContactPartiteEndpoints (P.stripHypergraph b) (base b) where
  part := fun x => ⟨P.stripPart b x,P.strip_projects b x.property⟩
  endpoint := P.stripEndpoint b
  part_endpoint := by
    intro e a
    exact Subtype.ext (Classical.choose_spec (P.strip_endpoint_exists b e a)).2
  carrier_eq := by
    intro e
    ext x
    constructor
    · intro hx
      let a : base b := ⟨P.vertex x.val,P.strip_projects b x.property⟩
      refine ⟨a,?_⟩
      apply Subtype.ext
      exact P.edge_inj e.val (Classical.choose_spec (P.strip_endpoint_exists b e a)).1 hx
        (Classical.choose_spec (P.strip_endpoint_exists b e a)).2
    · rintro ⟨a,rfl⟩
      exact (Classical.choose_spec (P.strip_endpoint_exists b e a)).1
  covered := P.strip_covered b

end ContactBaseProjection

namespace ContactPartiteEndpoints
variable {D : ContactHypergraphData V E I} {A : Type v}
    (P : ContactPartiteEndpoints D A) (N : Type)

noncomputable def lineTrainEmbedding
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (l : Combinatorics.Line E N) :
    ContactTrainEmbedding D (contactHeightOne E)
      (P.wordHypergraph N) (contactHeightOne (N → E)) where
  vertex := P.lineVertexEmb N l
  edge := P.lineEdgeEmb N l
  carrier_eq := P.line_carrier N l
  rel_iff := contactHeightOne_embedding_rel (P.lineEdgeEmb N l)
  strong := P.line_strong N hlin l

noncomputable def wordTrainFamily
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ContactDesignatedEmbeddings D (contactHeightOne E)
      (P.wordHypergraph N) (contactHeightOne (N → E)) where
  emb := P.lineTrainEmbedding N hlin
  vertex_eq := fun _ => rfl
  edge_eq := fun _ => rfl

/-- The word-base line construction satisfies the nonlinear
picture-step intersection hypothesis with its actual copy-edge
labels. -/
theorem word_pair_geometry
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (l k : Combinatorics.Line E N) (hne : l ≠ k)
    (u v : P.WordVertex N)
    (hu : u ∈ (P.wordHypergraph N).copyCarrier l ∩ (P.wordHypergraph N).copyCarrier k)
    (hv : v ∈ (P.wordHypergraph N).copyCarrier l ∩ (P.wordHypergraph N).copyCarrier k)
    (hp : P.wordPart N u ≠ P.wordPart N v) :
    ∃ e, e ∈ (P.wordHypergraph N).copyEdges l ∧ e ∈ (P.wordHypergraph N).copyEdges k ∧
      (P.wordHypergraph N).copyCarrier l ∩ (P.wordHypergraph N).copyCarrier k =
        (P.wordHypergraph N).edgeCarrier e :=
  P.line_pair_intersection N hlin l k hne u v hu hv hp

end ContactPartiteEndpoints
end StructuralRamsey.Girth
