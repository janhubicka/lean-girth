import Girth.ContactBaseProjection
import Girth.ContactDirectIncrement

/-! Exact real-carrier geometry for the direct forest increment.
The owner labels are core copies and core edges (the latter are
used only when no standard contains the edge). Every output piece
has a trace in the core that is short or an actual edge of that
piece. The proof uses the active strip projection, not output
mixed forests. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

theorem contact_image_subsingleton {U W : Type v} (f : U ↪ W)
    {A : Set U} (h : A.Subsingleton) : (f '' A).Subsingleton := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact congrArg f (h ha hb)

theorem contact_image_inter {U W : Type v} (f : U ↪ W)
    (A B : Set U) : f '' (A ∩ B) = f '' A ∩ f '' B := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u,hu.1,rfl⟩,⟨u,hu.2,rfl⟩⟩
  · rintro ⟨⟨u,hu,he⟩,⟨w,hw,he'⟩⟩
    have hw' := f.injective (he'.trans he.symm)
    subst w
    exact ⟨u,⟨hu,hw⟩,he⟩

namespace ContactJoinTree
variable {U W N : Type v} {F : N → Set U}

/-- Injectively carrying all vertices into an ambient set preserves
the very same join tree. Unused ambient vertices have empty fibres. -/
def mapVertices (T : ContactJoinTree F) (f : U ↪ W) :
    ContactJoinTree (fun n => f '' F n) where
  tree := T.tree
  isTree := T.isTree
  running := by
    intro x
    classical
    by_cases hx : x ∈ Set.range f
    · obtain ⟨u,rfl⟩ := hx
      have he : {n | f u ∈ f '' F n} = {n | u ∈ F n} := by
        ext n
        constructor
        · rintro ⟨a,ha,he⟩
          exact (f.injective he) ▸ ha
        · intro h
          exact ⟨u,h,rfl⟩
      change (T.tree.induce {n | f u ∈ f '' F n}).Preconnected
      rw [he]
      exact T.running u
    · letI : Subsingleton {n : N | x ∈ f '' F n} := ⟨by
        intro a b
        obtain ⟨u,_,he⟩ := a.property
        exact (hx ⟨u,he⟩).elim⟩
      exact SimpleGraph.Preconnected.of_subsingleton

end ContactJoinTree

namespace ContactTrainStrip
variable {m : ℕ} {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

def coreSet : Set A.Vertex := Set.range A.coreV

def ownerPiece (a : I ⊕ E) : Set A.Vertex :=
  match a with
  | .inl i => Set.range (A.stdV i)
  | .inr e => A.coreV '' D.edgeCarrier e

def localIndex (_A : ContactTrainStrip D L T S) : I ⊕ E → Type v
  | .inl _ => I₀ ⊕ E₀
  | .inr _ => PUnit.{v+1}

def localPiece : (a : I ⊕ E) → A.localIndex a → Set A.Vertex
  | .inl i => fun b => A.stdV i '' L.bottomCut.carrier b
  | .inr e => fun _ => A.coreV '' D.edgeCarrier e

theorem owner_trace (a : I ⊕ E) :
    A.ownerPiece a ∩ A.coreSet = A.coreV '' D.bottomCut.carrier a := by
  cases a with
  | inl i =>
    ext u
    constructor
    · rintro ⟨hu,⟨x,rfl⟩⟩
      exact ⟨x,(A.bottomPicture.toPictureData.std_core_vertex i x).mp hu,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(A.bottomPicture.toPictureData.std_core_vertex i x).mpr hx,⟨x,rfl⟩⟩
  | inr e =>
    apply Set.inter_eq_left.mpr
    rintro u ⟨x,_,rfl⟩
    exact ⟨x,rfl⟩

theorem owner_cross (a b : I ⊕ E) (hne : a ≠ b) :
    A.ownerPiece a ∩ A.ownerPiece b ⊆ A.coreSet := by
  intro u hu
  cases a with
  | inr e =>
    obtain ⟨x,_,he⟩ := hu.1
    exact ⟨x,he⟩
  | inl i =>
    cases b with
    | inr e =>
      obtain ⟨x,_,he⟩ := hu.2
      exact ⟨x,he⟩
    | inl j =>
      exact A.bottomPicture.toPictureData.shared_vertex i j
        (fun he => hne (congrArg Sum.inl he)) u hu.1 hu.2

theorem owner_intersection (a b : I ⊕ E) (hne : a ≠ b) :
    A.ownerPiece a ∩ A.ownerPiece b =
      A.coreV '' (D.bottomCut.carrier a ∩ D.bottomCut.carrier b) := by
  rw [contact_image_inter,← A.owner_trace a,← A.owner_trace b]
  ext u
  constructor
  · intro hu
    have hc := A.owner_cross a b hne hu
    exact ⟨⟨hu.1,hc⟩,⟨hu.2,hc⟩⟩
  · intro hu
    exact ⟨hu.1.1,hu.2.1⟩

/-- The full outer separator, if nontrivial, is an actual shared
core edge occurring in both local systems. This uses pairwise
mixed forests only for distinct core owners. -/
theorem owner_separator (hD : D.bottomCut.ZeroPairwise)
    (a b : I ⊕ E) (hne : a ≠ b) :
    (A.ownerPiece a ∩ A.ownerPiece b).Subsingleton ∨
      ∃ e, A.ownerPiece a ∩ A.ownerPiece b = A.coreV '' D.edgeCarrier e ∧
        e ∈ D.bottomCut.edges a ∧ e ∈ D.bottomCut.edges b := by
  rw [A.owner_intersection a b hne]
  rcases hD a b hne with hs | ⟨e,ha,hb,he⟩
  · exact Or.inl (contact_image_subsingleton A.coreV hs)
  · exact Or.inr ⟨e,congrArg (fun s : Set V => A.coreV '' s) he,ha,hb⟩

theorem local_core_edge (a : I ⊕ E) (e : E)
    (he : e ∈ D.bottomCut.edges a) :
    ∃ j : A.localIndex a, A.localPiece a j = A.coreV '' D.edgeCarrier e := by
  cases a with
  | inl i =>
    obtain ⟨f,hf⟩ := (A.edge_domain i e).mpr he
    exact ⟨Sum.inr f,A.shared_edge_carrier i f e hf⟩
  | inr f =>
    have hef : e = f := he
    subst f
    exact ⟨PUnit.unit,rfl⟩

/-- A join tree for a selected family of core owners lifts to their
full constituents: private points cannot connect different owners. -/
noncomputable def owner_joinTree {N : Type v} (sel : N ↪ I ⊕ E)
    (T₀ : ContactJoinTree (fun n => D.bottomCut.carrier (sel n))) :
    ContactJoinTree (fun n => A.ownerPiece (sel n)) := by
  let T₁ := T₀.mapVertices A.coreV
  have he : (fun n => A.ownerPiece (sel n) ∩ A.coreSet) =
      (fun n => A.coreV '' D.bottomCut.carrier (sel n)) := by
    funext n
    exact A.owner_trace (sel n)
  have T₂ : ContactJoinTree (fun n => A.ownerPiece (sel n) ∩ A.coreSet) :=
    he.symm ▸ T₁
  apply T₂.restoreOutside
  intro x hx n hn k hk
  by_contra hne
  exact hx (A.owner_cross _ _ (fun he => hne (sel.injective he)) ⟨hn,hk⟩)

/-- The mixed pieces of the output have the natural owner assignment:
every lifted designated copy uses its standard, and every edge
uses a standard containing it, or its core-edge label. -/
theorem piece_has_owner (a : (I × I₀) ⊕ A.Edge) :
    ∃ b : I ⊕ E, (A.outputHypergraph.bottomCut.carrier a ⊆ A.ownerPiece b) ∧
      ∃ j : A.localIndex b,
        A.outputHypergraph.bottomCut.carrier a = A.localPiece b j := by
  cases a with
  | inl c =>
    rcases c with ⟨i,j⟩
    exact ⟨Sum.inl i,fun x hx => by obtain ⟨u,_,he⟩ := hx; exact ⟨u,he⟩,
      Sum.inl j,rfl⟩
  | inr e =>
    by_cases h : ∃ i f, A.stdE i f = e
    · obtain ⟨i,f,rfl⟩ := h
      have he : A.outputHypergraph.edgeCarrier (A.stdE i f) =
          A.stdV i '' L.edgeCarrier f := by
        have h := A.bottomPicture.output_carrier_standard i f
        rw [A.bottomPicture_output_eq] at h
        exact h
      exact ⟨Sum.inl i,fun x hx => by
          change x ∈ A.outputHypergraph.edgeCarrier (A.stdE i f) at hx
          rw [he] at hx
          obtain ⟨u,_,h⟩ := hx
          exact ⟨u,h⟩,
        Sum.inr f,he⟩
    · rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨f,rfl⟩ | ⟨i,f,hf⟩
      · have he : A.outputHypergraph.edgeCarrier (A.coreE f) =
            A.coreV '' D.edgeCarrier f := by
          have h := A.bottomPicture.output_carrier_core f
          rw [A.bottomPicture_output_eq] at h
          exact h
        exact ⟨Sum.inr f,by
            change A.outputHypergraph.edgeCarrier (A.coreE f) ⊆ A.coreV '' D.edgeCarrier f
            rw [he],
          PUnit.unit,he⟩
      · exact (h ⟨i,f,hf⟩).elim

/-- The actual trace of a standard member is the image of its
active-strip trace. -/
theorem std_trace_image (i : I) (F : Set V₀) :
    (A.stdV i '' F) ∩ A.coreSet =
      A.stdV i '' (F ∩ {x | ∃ y, A.vertexGlue i x = some y}) := by
  ext u
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,⟨y,hy⟩⟩
    exact ⟨x,⟨hx,⟨y,(contactStandardEmb_eq_core A.vertexGlue A.vertex_inj i x y).mp hy.symm⟩⟩,rfl⟩
  · rintro ⟨x,⟨hx,⟨y,hy⟩⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,⟨y,((contactStandardEmb_eq_core A.vertexGlue A.vertex_inj i x y).mpr hy).symm⟩⟩

theorem std_piece_trace {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hlin : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (i : I) (a : I₀ ⊕ E₀) :
    (A.stdV i '' L.bottomCut.carrier a ∩ A.coreSet).Subsingleton ∨
      ∃ e f, f ∈ L.bottomCut.edges a ∧ A.edgeGlue i f = some e ∧
        A.stdV i '' L.bottomCut.carrier a ∩ A.coreSet = A.coreV '' D.edgeCarrier e := by
  rw [A.std_trace_image]
  rcases A.stripTrace_of_projection P b hA hlin i a with hs | ⟨f,e,hf,he,ht⟩
  · exact Or.inl (contact_image_subsingleton (A.stdV i) hs)
  · refine Or.inr ⟨e,f,hf,he,?_⟩
    rw [ht]
    exact A.shared_edge_carrier i f e he

end ContactTrainStrip
end StructuralRamsey.Girth
