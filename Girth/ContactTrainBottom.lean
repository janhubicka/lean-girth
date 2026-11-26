import Girth.ContactGeneratedTrain
import Girth.ContactWagonRelabel
import Girth.ContactPictureStrong
import Girth.ContactBottomOwners

/-! At the bottom level wagons are the individual edges. Normalize
their labels literally to the edge type, then use the established
bottom preservation theorem. The normalization is not a quotient
of vertex carriers and cannot merge any distinct edge labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ : Type v}

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I)

def bottomCut : OrderOneData V E I E := D.atCut id

theorem relabel_atCut {P R : Type v} (p : E → P) (e : P ≃ R) :
    (D.atCut p).relabelWagons e = D.atCut (e ∘ p) := rfl

theorem relabel_bottomCut {P : Type v} (p : E ≃ P) :
    D.bottomCut.relabelWagons p = D.atCut p := rfl

end ContactHypergraphData

namespace ContactTrainData
variable {m : ℕ} (T : ContactTrainData E m)

noncomputable def bottomEquiv : E ≃ T.Wagon ⟨0,by omega⟩ :=
  Equiv.ofBijective _ ⟨T.bottom,T.surj ⟨0,by omega⟩⟩

theorem bottomEquiv_apply (e : E) :
    T.bottomEquiv e = T.parent ⟨0,by omega⟩ e := rfl

theorem bottom_systemGirth_iff (D : ContactHypergraphData V E I) (q : ℕ) :
    (D.atCut (T.parent ⟨0,by omega⟩)).ContactSystemGirthGT q ↔
      D.bottomCut.ContactSystemGirthGT q := by
  have h := D.bottomCut.relabel_systemGirth_iff T.bottomEquiv (q := q)
  rw [D.relabel_bottomCut T.bottomEquiv] at h
  exact h

end ContactTrainData

namespace ContactTrainStrip
variable {m : ℕ}
    {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

/-- The bottom tagged picture uses the same gluing on edges and
wagons, and the same real-vertex gluing as every other cut. -/
def bottomPicture : ContactTaggedPicture D.bottomCut L.bottomCut where
  vertexGlue := A.vertexGlue
  edgeGlue := A.edgeGlue
  wagonGlue := A.edgeGlue
  vertex_inj := A.vertex_inj
  edge_inj := A.edge_inj
  wagon_inj := A.edge_inj
  vertex_domain := A.vertex_domain
  edge_domain := A.edge_domain
  shared_edge_carrier := A.shared_edge_carrier
  shared_parent := fun _ _ _ h => h
  wagon_domain := by
    intro i e
    rw [A.edge_domain]
    constructor
    · intro he
      exact ⟨e,he,rfl⟩
    · rintro ⟨f,hf,he⟩
      change f = e at he
      exact he ▸ hf
  core_parent_surj := Function.surjective_id
  old_parent_surj := Function.surjective_id

theorem bottomPicture_parent (e : A.Edge) :
    A.bottomPicture.output.parent e = e := by
  rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨f,rfl⟩ | ⟨i,f,rfl⟩
  · exact A.bottomPicture.output_parent_core f
  · exact A.bottomPicture.output_parent_standard i f

/-- The identity-parent view and every labelled cut have the same
underlying hypergraph. In particular the normalized bottom output
is literally the bottom cut of the output hypergraph. -/
theorem bottomPicture_output_eq :
    A.bottomPicture.output = A.outputHypergraph.bottomCut := by
  have hp : A.bottomPicture.output.parent = id := by
    funext e
    exact A.bottomPicture_parent e
  unfold ContactHypergraphData.bottomCut ContactHypergraphData.atCut outputHypergraph
    ContactTaggedPicture.output
  congr 1 <;> first
  | rfl
  | exact hp
  | (funext e; rcases e with ⟨t,ht⟩; cases t <;> rfl)

/-- The strong active-strip assumption is independent of the level. -/
def StripStrong : Prop :=
  ∀ i f, (L.edgeCarrier f ∩ {x | ∃ y, A.vertexGlue i x = some y}).Nontrivial →
    ∃ e, A.edgeGlue i f = some e

theorem stripStrong_atCut (h : A.StripStrong) (μ : Fin (m+1)) :
    (A.atCut μ).StripStrong := h

theorem stripStrong_bottom (h : A.StripStrong) : A.bottomPicture.StripStrong := h

/-- One-edge trace property in the old picture. If an old designated
copy contains a shared edge, all its vertices lying in the common
strip lie on that edge. This is the exact conclusion of the
transversal projection/absorption observation. -/
def StripAbsorption : Prop :=
  ∀ i j f, f ∈ L.copyEdges j → (∃ e, A.edgeGlue i f = some e) →
    ∀ x, x ∈ L.copyCarrier j → (∃ y, A.vertexGlue i x = some y) →
    x ∈ L.edgeCarrier f

theorem bottomAbsorption_of_strip (h : A.StripAbsorption) :
    A.bottomPicture.toPictureData.BottomAbsorption := by
  intro c e he x hx
  rcases c with ⟨i,j⟩
  change A.coreE e ∈ A.stdE i '' L.copyEdges j at he
  change A.coreV x ∈ A.stdV i '' L.copyCarrier j at hx
  obtain ⟨f,hf,hfe⟩ := he
  obtain ⟨y,hy,hyx⟩ := hx
  have hge := (contactStandardEmb_eq_core A.edgeGlue A.edge_inj i f e).mp hfe
  have hgv := (contactStandardEmb_eq_core A.vertexGlue A.vertex_inj i y x).mp hyx
  have hyf := h i j f hf ⟨e,hge⟩ y hy ⟨x,hgv⟩
  let P := A.bottomPicture
  have hmem : P.coreV x ∈ P.output.edgeCarrier (P.stdE i f) := by
    rw [P.output_carrier_standard]
    exact ⟨y,hyf,hyx⟩
  have heq : P.stdE i f = P.coreE e := hfe
  rw [heq,P.output_carrier_core] at hmem
  obtain ⟨z,hz,hzx⟩ := hmem
  exact (P.coreV.injective hzx) ▸ hz

end ContactTrainStrip
end StructuralRamsey.Girth
