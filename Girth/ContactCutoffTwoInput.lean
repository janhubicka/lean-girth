import Girth.ContactCutoffTwoChosen
import Girth.ContactVaryingDisjoint
import Girth.ContactSelectionTransport

/-! The actual common shorter-train input and the original train
embeddings into its canonical filling. The word-base construction
supplies the template embeddings. The shorter-train Ramsey theorem
will be applied to the constructed input, not to unrelated labels. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X F J C : Type v}

/-- A template with its family of lines on the disjoint original
first wagons. Each line determines one padded component. -/
structure ContactCutoffTwoInput {m : ℕ}
    (D : ContactHypergraphData V E I) (T : ContactTrainData E (m+1))
    (L : ContactHypergraphData X F J) (C : Type v) where
  tail_pos : 0 < m
  cover : ∀ x, ∃ f, x ∈ L.edgeCarrier f
  nonempty : Nonempty F
  pad : C → ContactWagonPadding
    (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier X
  line : (c : C) → (pad c).TemplateEmbedding L

namespace ContactCutoffTwoInput
variable {m : ℕ} {D : ContactHypergraphData V E I}
    {T : ContactTrainData E (m+1)} {L : ContactHypergraphData X F J}
    (A : ContactCutoffTwoInput D T L C)

abbrev Component (c : C) := (A.pad c).Vertex
abbrev Vertex := Sigma A.Component
abbrev OldEdge := C × T.FirstWagon
abbrev Edge := A.OldEdge × F

noncomputable def source : ContactHypergraphData A.Vertex A.OldEdge PEmpty.{v+1} :=
  ContactHypergraphData.varyingDisjoint (fun c => (A.pad c).paddedHypergraph)

noncomputable def sourceTrain : ContactTrainData A.OldEdge m :=
  T.shorterTrain.disjointTrain C A.tail_pos

noncomputable def fill : ContactFilling A.source L where
  place := fun p => ((A.pad p.1).place p.2).trans (contactComponentEmb p.1)
  range_eq := by
    intro p
    change Set.range (fun x => contactComponentEmb p.1 ((A.pad p.1).place p.2 x)) =
      contactComponentEmb p.1 '' Set.range ((A.pad p.1).place p.2)
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨_,⟨y,rfl⟩,rfl⟩
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
  template_cover := A.cover
  template_nonempty := A.nonempty

noncomputable def filled : ContactHypergraphData A.Vertex A.Edge PEmpty.{v+1} :=
  A.fill.output

noncomputable def filledTrain : ContactTrainData A.Edge (m+1) :=
  A.fill.fillTrain A.sourceTrain

noncomputable def localFill (c : C) : ContactFilling (A.pad c).paddedHypergraph L :=
  (A.pad c).filling L A.cover A.nonempty

def localEdge (c : C) : T.FirstWagon × F ↪ A.Edge where
  toFun p := ((c,p.1),p.2)
  inj' := by
    intro p r h
    exact Prod.ext (congrArg (fun e : A.Edge => e.1.2) h)
      (congrArg Prod.snd h)

theorem local_carrier (c : C) (p : T.FirstWagon × F) :
    A.filled.edgeCarrier (A.localEdge c p) =
      contactComponentEmb c '' (A.localFill c).output.edgeCarrier p := by
  change (fun x => contactComponentEmb c ((A.pad c).place p.1 x)) ''
      L.edgeCarrier p.2 = contactComponentEmb c '' ((A.pad c).place p.1 '' L.edgeCarrier p.2)
  rw [Set.image_image]

theorem edge_component (p : A.Edge) (x : A.Vertex) (hx : x ∈ A.filled.edgeCarrier p) :
    x.1 = p.1.1 := by
  obtain ⟨y,_,he⟩ := hx
  exact (congrArg Sigma.fst he).symm

/-- Exact relations of each local filled component in the common
filled input. Only the universal top is identified across
components. -/
theorem local_rel (c : C) (μ : Fin (m+2)) (e f : T.FirstWagon × F) :
    A.filledTrain.parent μ (A.localEdge c e) = A.filledTrain.parent μ (A.localEdge c f) ↔
      ((A.localFill c).fillTrain T.shorterTrain).parent μ e =
        ((A.localFill c).fillTrain T.shorterTrain).parent μ f := by
  refine Fin.cases ?_ (fun ν => ?_) μ
  · change A.localEdge c e = A.localEdge c f ↔ e = f
    exact ⟨fun h => (A.localEdge c).injective h,fun h => congrArg (A.localEdge c) h⟩
  · change A.sourceTrain.parent ν (c,e.1) = A.sourceTrain.parent ν (c,f.1) ↔
      T.shorterTrain.parent ν e.1 = T.shorterTrain.parent ν f.1
    constructor
    · intro h
      have h' := Quotient.exact h
      change ν.val = m ∨ c = c ∧ T.shorterTrain.parent ν e.1 =
        T.shorterTrain.parent ν f.1 at h'
      rcases h' with ht | ⟨_,he⟩
      · have hν : ν = (⟨m,by omega⟩ : Fin (m+1)) := Fin.ext ht
        rw [hν]
        exact T.shorterTrain.top _ _
      · exact he
    · intro h
      exact Quotient.sound (Or.inr ⟨rfl,h⟩)

/-- Every actual local filled component embeds strongly in the
disjoint common filling. -/
noncomputable def componentEmbedding (c : C) :
    ContactTrainEmbedding (A.localFill c).output ((A.localFill c).fillTrain T.shorterTrain)
      A.filled A.filledTrain where
  vertex := contactComponentEmb c
  edge := A.localEdge c
  carrier_eq := A.local_carrier c
  rel_iff := A.local_rel c
  strong := by
    intro p hn
    obtain ⟨x,hx,_,_,_⟩ := hn
    obtain ⟨u,hu⟩ := hx.2
    have h := (congrArg Sigma.fst hu).symm.trans (A.edge_component p x hx.1)
    rcases p with ⟨⟨i,r⟩,f⟩
    change c = i at h
    subst i
    exact ⟨(r,f),rfl⟩

noncomputable def originalLocal (c : C) :
    ContactTrainEmbedding D T (A.localFill c).output
      ((A.localFill c).fillTrain T.shorterTrain) where
  vertex := (A.pad c).oldVertex
  edge := (A.line c).chosenEdge
  carrier_eq := (A.line c).chosen_carrier A.cover A.nonempty
  rel_iff := (A.line c).chosen_rel A.cover A.nonempty
  strong := (A.line c).chosen_strong A.cover A.nonempty

noncomputable def original (c : C) : ContactTrainEmbedding D T A.filled A.filledTrain :=
  (A.originalLocal c).comp (A.componentEmbedding c)

/-- A positive proper wagon of the common filled input belongs
to a unique padded component. -/
theorem proper_component (μ : Fin (m+2)) (hp : 0 < μ.val) (ht : μ.val < m+1)
    (e f : A.Edge) (h : A.filledTrain.parent μ e = A.filledTrain.parent μ f) :
    e.1.1 = f.1.1 := by
  revert hp ht h
  refine Fin.cases ?_ (fun ν => ?_) μ
  · intro hp
    change 0 < 0 at hp
    omega
  · intro _ ht he
    change A.sourceTrain.parent ν e.1 = A.sourceTrain.parent ν f.1 at he
    have he' := Quotient.exact he
    change ν.val = m ∨ e.1.1 = f.1.1 ∧
      T.shorterTrain.parent ν e.1.2 = T.shorterTrain.parent ν f.1.2 at he'
    rcases he' with htop | ⟨h,_⟩
    · change ν.val+1 < m+1 at ht
      omega
    · exact h

/-- The actual selected family in the source filling. Both
partition owners are the explicit component tags. -/
noncomputable def selection : ContactLocalSelection A.filled A.filledTrain C where
  vertexOwner := Sigma.fst
  edgeOwner := fun e => e.1.1
  edge_owner := A.edge_component
  chosenV := fun c => Set.range (A.original c).vertex
  chosenE := fun c => Set.range (A.original c).edge
  vertex_sub := by
    rintro c x ⟨u,rfl⟩
    rfl
  edge_sub := by
    rintro c e ⟨f,rfl⟩
    rfl
  edge_vertices := by
    rintro c e ⟨f,rfl⟩
    exact (A.original c).vertex_range_of_edge f
  strong := fun c e _ he => (A.original c).strong e he
  proper_owner := A.proper_component
  incidence := by
    intro μ hp ht c e x he hx hxchosen
    rcases e with ⟨⟨i,p⟩,f⟩
    change i = c at he
    subst i
    obtain ⟨u,rfl⟩ := hxchosen
    let v := (A.pad c).oldVertex u
    have hx' : v ∈ (A.localFill c).output.edgeCarrier (p,f) :=
      ((A.componentEmbedding c).mem_edge_image (p,f) v).mp hx
    revert hp ht
    refine Fin.cases ?_ (fun ν => ?_) μ
    · intro hp
      change 0 < 0 at hp
      omega
    · intro _ _
      have hmem : (A.pad c).oldVertex u ∈
          (((A.line c).Filled A.cover A.nonempty).atCut
            (((A.localFill c).fillTrain T.shorterTrain).parent ν.succ)).contactWagonCarrier
              (T.shorterParent ν p) :=
        ⟨(p,f),rfl,hx'⟩
      obtain ⟨a,ha,hu⟩ := (A.line c).chosen_incidence A.cover A.nonempty ν u
        (T.shorterParent ν p) hmem
      refine ⟨(A.original c).edge a,⟨a,rfl⟩,?_,?_⟩
      · apply (A.local_rel c ν.succ ((A.line c).chosenEdge a) (p,f)).mpr
        change T.shorterParent ν ((A.pad c).first a) = T.shorterParent ν p
        rw [T.shorterParent_first]
        exact ha
      · exact ((A.original c).mem_edge_image a u).mpr hu
  intersection := by
    intro μ hp ht c e f x he hf hne hx hy
    rcases e with ⟨⟨i,p⟩,a⟩
    rcases f with ⟨⟨j,r⟩,b⟩
    change i = c at he
    change j = c at hf
    subst i
    subst j
    rw [show A.filled.edgeCarrier ((c,p),a) =
      contactComponentEmb c '' (A.localFill c).output.edgeCarrier (p,a) from
      A.local_carrier c (p,a)] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    have hy' := ((A.componentEmbedding c).mem_edge_image (r,b) z).mp hy
    revert hp ht hne
    refine Fin.cases ?_ (fun ν => ?_) μ
    · intro hp
      change 0 < 0 at hp
      omega
    · intro _ _ hne
      have hneq : T.shorterParent ν p ≠ T.shorterParent ν r := by
        intro he
        exact hne ((A.local_rel c ν.succ (p,a) (r,b)).mpr he)
      have hz' := (A.line c).wagon_intersection_chosen A.cover A.nonempty ν
        (T.shorterParent ν p) (T.shorterParent ν r) hneq
        ⟨⟨(p,a),rfl,hz⟩,⟨(r,b),rfl,hy'⟩⟩
      obtain ⟨u,hu⟩ := hz'
      exact ⟨u,congrArg (contactComponentEmb c) hu⟩

end ContactCutoffTwoInput
end StructuralRamsey.Girth
