import Girth.ContactIncrementGeometry

/-! The actual labelled output pieces and their traces. The
local representation preserves edge labels, which is essential:
a carrier equality alone is not the allowed-intersection condition
of a mixed forest. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

namespace ContactTrainStrip
variable {m : ℕ} {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)

def stdPieceLabel (i : I) : (I₀ ⊕ E₀) ↪ ((I × I₀) ⊕ A.Edge) where
  toFun a := match a with
    | .inl j => Sum.inl (i,j)
    | .inr f => Sum.inr (A.stdE i f)
  inj' := by
    intro a b h
    cases a with
    | inl j =>
      cases b with
      | inl k =>
        exact congrArg Sum.inl (congrArg Prod.snd (Sum.inl.inj h))
      | inr f => cases h
    | inr e =>
      cases b with
      | inl j => cases h
      | inr f => exact congrArg Sum.inr ((A.stdE i).injective (Sum.inr.inj h))

def localOutputLabel : (a : I ⊕ E) → A.localIndex a → (I × I₀) ⊕ A.Edge
  | .inl i => fun j => A.stdPieceLabel i j
  | .inr e => fun _ => Sum.inr (A.coreE e)

theorem output_carrier_std (i : I) (a : I₀ ⊕ E₀) :
    A.outputHypergraph.bottomCut.carrier (A.stdPieceLabel i a) =
      A.stdV i '' L.bottomCut.carrier a := by
  cases a with
  | inl j => rfl
  | inr f =>
    have he := A.bottomPicture.output_carrier_standard i f
    rw [A.bottomPicture_output_eq] at he
    exact he

theorem output_edges_std (i : I) (a : I₀ ⊕ E₀) :
    A.outputHypergraph.bottomCut.edges (A.stdPieceLabel i a) =
      A.stdE i '' L.bottomCut.edges a := by
  cases a with
  | inl j => rfl
  | inr f =>
    change ({A.stdE i f} : Set A.Edge) = A.stdE i '' ({f} : Set E₀)
    simp

theorem output_carrier_core_edge (e : E) :
    A.outputHypergraph.bottomCut.carrier (Sum.inr (A.coreE e)) =
      A.coreV '' D.edgeCarrier e := by
  have he := A.bottomPicture.output_carrier_core e
  rw [A.bottomPicture_output_eq] at he
  exact he

theorem localOutput_carrier (b : I ⊕ E) (j : A.localIndex b) :
    A.outputHypergraph.bottomCut.carrier (A.localOutputLabel b j) =
      A.localPiece b j := by
  cases b with
  | inl i => exact A.output_carrier_std i j
  | inr e => exact A.output_carrier_core_edge e

theorem localPiece_subset_owner (b : I ⊕ E) (j : A.localIndex b) :
    A.localPiece b j ⊆ A.ownerPiece b := by
  cases b with
  | inl i =>
    rintro u ⟨x,_,rfl⟩
    exact ⟨x,rfl⟩
  | inr e => exact Set.Subset.rfl

theorem output_has_localLabel (a : (I × I₀) ⊕ A.Edge) :
    ∃ b : I ⊕ E, ∃ j : A.localIndex b, A.localOutputLabel b j = a := by
  cases a with
  | inl p =>
    exact ⟨Sum.inl p.1,Sum.inl p.2,by cases p; rfl⟩
  | inr e =>
    by_cases h : ∃ i f, A.stdE i f = e
    · obtain ⟨i,f,hf⟩ := h
      exact ⟨Sum.inl i,Sum.inr f,congrArg Sum.inr hf⟩
    · rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨f,hf⟩ | ⟨i,f,hf⟩
      · exact ⟨Sum.inr f,PUnit.unit,congrArg Sum.inr hf⟩
      · exact (h ⟨i,f,hf⟩).elim

/-- Full trace property for actual output pieces, with edge
membership retained in each nontrivial trace. -/
theorem output_piece_trace {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hlin : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (a : (I × I₀) ⊕ A.Edge) :
    (A.outputHypergraph.bottomCut.carrier a ∩ A.coreSet).Subsingleton ∨
      ∃ e, A.coreE e ∈ A.outputHypergraph.bottomCut.edges a ∧
        A.outputHypergraph.bottomCut.carrier a ∩ A.coreSet = A.coreV '' D.edgeCarrier e := by
  obtain ⟨owner,j,rfl⟩ := A.output_has_localLabel a
  cases owner with
  | inl i =>
    change (A.outputHypergraph.bottomCut.carrier (A.stdPieceLabel i j) ∩ A.coreSet).Subsingleton ∨ _
    rw [A.output_carrier_std,A.output_edges_std]
    rcases A.std_piece_trace P b hA hlin i j with hs | ⟨e,f,hf,hg,he⟩
    · exact Or.inl hs
    · exact Or.inr ⟨e,⟨f,hf,A.shared_edge_eq i f e hg⟩,he⟩
  | inr e =>
    change (A.outputHypergraph.bottomCut.carrier (Sum.inr (A.coreE e)) ∩ A.coreSet).Subsingleton ∨ _
    rw [A.output_carrier_core_edge]
    right
    refine ⟨e,rfl,Set.inter_eq_left.mpr ?_⟩
    rintro x ⟨u,_,rfl⟩
    exact ⟨u,rfl⟩

/-- Images of the core edges are linear. -/
theorem embedded_core_linear
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ∀ e f : E, e ≠ f →
      ((A.coreV '' D.edgeCarrier e) ∩ (A.coreV '' D.edgeCarrier f)).Subsingleton := by
  intro e f hne
  rw [← contact_image_inter]
  exact contact_image_subsingleton A.coreV (hlin e f hne)

/-- Image girth: no new labelled Berge cycle can be created by an
injective map on vertices. -/
theorem embedded_core_girth {q : ℕ} (hg : LabelledGirthGT D.edgeCarrier q) :
    LabelledGirthGT (fun e => A.coreV '' D.edgeCarrier e) q := by
  classical
  rintro ⟨C,hq⟩
  have hex : ∀ i, ∃ x, x ∈ D.edgeCarrier (C.label i) ∧ A.coreV x = C.vertex i :=
    fun i => C.left_mem i
  choose x hx using hex
  have hright : ∀ i, x i ∈ D.edgeCarrier (C.label (cyclicSucc i)) := by
    intro i
    obtain ⟨y,hy,he⟩ := C.right_mem i
    exact (A.coreV.injective (he.trans (hx i).2.symm)) ▸ hy
  let K : LabelledBergeCycle D.edgeCarrier := {
    length := C.length
    hlength := C.hlength
    label := C.label
    vertex := x
    label_injective := C.label_injective
    vertex_injective := by
      intro i j he
      exact C.vertex_injective ((hx i).2.symm.trans ((congrArg A.coreV he).trans (hx j).2))
    left_mem := fun i => (hx i).1
    right_mem := hright
  }
  exact hg ⟨K,hq⟩

/-- For any choice of owner representation of the two pieces,
allowed pairwise intersections follow from the local old
condition and the actual core trace geometry. -/
theorem output_pairwise_of_trace {base : B → Set X} (P : ContactBaseProjection L base)
    (b : B) (hA : A.ActiveOver P b)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (hL : L.bottomCut.ZeroPairwise) :
    A.outputHypergraph.bottomCut.ZeroPairwise := by
  classical
  let H := A.outputHypergraph.bottomCut
  intro a c hne
  obtain ⟨i,j,ha⟩ := A.output_has_localLabel a
  obtain ⟨k,l,hc⟩ := A.output_has_localLabel c
  by_cases hik : i = k
  · subst k
    cases i with
    | inr e =>
      have he : j = l := Subsingleton.elim _ _
      exact (hne (ha.symm.trans ((congrArg (A.localOutputLabel (Sum.inr e)) he).trans hc))).elim
    | inl i =>
      have hjl : j ≠ l := fun he =>
        hne (ha.symm.trans ((congrArg (A.localOutputLabel (Sum.inl i)) he).trans hc))
      change A.stdPieceLabel i j = a at ha
      change A.stdPieceLabel i l = c at hc
      rw [← ha,← hc,A.output_carrier_std,A.output_carrier_std,
        ← contact_image_inter]
      rcases hL j l hjl with hs | ⟨f,hf,hf',he⟩
      · exact Or.inl (contact_image_subsingleton (A.stdV i) hs)
      · right
        refine ⟨A.stdE i f,?_,?_,?_⟩
        · rw [A.output_edges_std]
          exact ⟨f,hf,rfl⟩
        · rw [A.output_edges_std]
          exact ⟨f,hf',rfl⟩
        · rw [he]
          exact (A.output_carrier_std i (Sum.inr f)).symm
  · have haSub : H.carrier a ⊆ A.ownerPiece i := by
      rw [← ha,A.localOutput_carrier]
      exact A.localPiece_subset_owner i j
    have hcSub : H.carrier c ⊆ A.ownerPiece k := by
      rw [← hc,A.localOutput_carrier]
      exact A.localPiece_subset_owner k l
    have hcore : H.carrier a ∩ H.carrier c ⊆ A.coreSet :=
      fun x hx => A.owner_cross i k hik ⟨haSub hx.1,hcSub hx.2⟩
    by_cases hs : (H.carrier a ∩ H.carrier c).Subsingleton
    · exact Or.inl hs
    obtain ⟨x,hx,y,hy,hxy⟩ := Set.not_subsingleton_iff.mp hs
    rcases A.output_piece_trace P b hA hbase a with h | ⟨e,hea,he⟩
    · exact (hxy (h ⟨hx.1,hcore hx⟩ ⟨hy.1,hcore hy⟩)).elim
    rcases A.output_piece_trace P b hA hbase c with h | ⟨f,hfc,hf⟩
    · exact (hxy (h ⟨hx.2,hcore hx⟩ ⟨hy.2,hcore hy⟩)).elim
    have hEq : e = f := by
      by_contra hne
      apply hxy
      apply A.embedded_core_linear hlin e f hne
      · exact ⟨he ▸ (show x ∈ H.carrier a ∩ A.coreSet from ⟨hx.1,hcore hx⟩),
          hf ▸ (show x ∈ H.carrier c ∩ A.coreSet from ⟨hx.2,hcore hx⟩)⟩
      · exact ⟨he ▸ (show y ∈ H.carrier a ∩ A.coreSet from ⟨hy.1,hcore hy⟩),
          hf ▸ (show y ∈ H.carrier c ∩ A.coreSet from ⟨hy.2,hcore hy⟩)⟩
    subst f
    refine Or.inr ⟨A.coreE e,hea,hfc,?_⟩
    change H.carrier a ∩ H.carrier c = H.carrier (Sum.inr (A.coreE e))
    rw [A.output_carrier_core_edge]
    ext z
    constructor
    · intro hz
      exact he ▸ (show z ∈ H.carrier a ∩ A.coreSet from ⟨hz.1,hcore hz⟩)
    · intro hz
      have hza : z ∈ H.carrier a ∩ A.coreSet := he.symm ▸ hz
      have hzc : z ∈ H.carrier c ∩ A.coreSet := hf.symm ▸ hz
      exact ⟨hza.1,hzc.1⟩

end ContactTrainStrip
end StructuralRamsey.Girth
