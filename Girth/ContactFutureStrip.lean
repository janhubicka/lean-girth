import Girth.ContactProjectionPreservation
import Girth.ContactSplitRefinementGeometry
import Girth.ContactIncrementPieces

/-! Actual future strips of a picture. Their edges are precisely
pairs (standard, old strip edge), because the active edge is
different. All intersections across those standards are in the
core copies and project to the single common base part. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I V₀ E₀ I₀ X B : Type v}

namespace ContactTrainStrip
variable {m : ℕ} {D : ContactHypergraphData V E I} {L : ContactHypergraphData V₀ E₀ I₀}
    {T : ContactTrainData E m} {S : ContactTrainData E₀ m}
    (A : ContactTrainStrip D L T S)
variable {base : B → Set X} (P : ContactBaseProjection L base) (b c : B)
    (hA : A.ActiveOver P b) (hne : c ≠ b)

abbrev OldStripEdge (_A : ContactTrainStrip D L T S) := {f : E₀ // P.edge f = c}
abbrev NewStripEdge := {f : A.Edge // A.outputProjectionEdge P b f = c}

def oldStripInclusion : A.OldStripEdge P c ↪ E₀ := ⟨Subtype.val,Subtype.val_injective⟩

/-- A future-strip edge of one standard is never glued to a core
edge. Two different standard labels therefore give distinct edges. -/
theorem future_not_core (i : I) (f : A.OldStripEdge P c) :
    A.stdE i f.val ∉ Set.range A.coreE := by
  rintro ⟨e,he⟩
  have hg := (contactStandardEmb_eq_core A.edgeGlue A.edge_inj i f.val e).mp he.symm
  exact hne (f.property.symm.trans ((hA.edge_domain i f.val).mp ⟨e,hg⟩))

theorem future_edge_injective :
    Function.Injective (fun p : I × A.OldStripEdge P c => A.stdE p.1 p.2.val) := by
  intro u w he
  rcases u with ⟨i,f⟩
  rcases w with ⟨j,g⟩
  by_cases hij : i = j
  · subst j
    exact Prod.ext rfl (Subtype.ext ((A.stdE i).injective he))
  · have hx := contactGlued_shared A.edgeGlue A.edge_inj i j hij (A.stdE i f.val)
      ⟨f.val,rfl⟩ ⟨g.val,he.symm⟩
    exact (A.future_not_core P b c hA hne i f hx).elim

noncomputable def futureEdgeEquiv : (I × A.OldStripEdge P c) ≃ A.NewStripEdge P b c := by
  let f : I × A.OldStripEdge P c → A.NewStripEdge P b c := fun p =>
    ⟨A.stdE p.1 p.2.val,(A.projection_edge_std P b hA p.1 p.2.val).trans p.2.property⟩
  have hi : Function.Injective f := fun a b he =>
    A.future_edge_injective P b c hA hne (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    rintro ⟨e,he⟩
    rcases contactGlued_cover A.edgeGlue A.edge_inj e with ⟨g,hg⟩ | ⟨i,g,hg⟩
    · have hh : A.outputProjectionEdge P b (A.coreE g) = c := hg.symm ▸ he
      rw [A.projection_edge_core] at hh
      exact (hne hh.symm).elim
    · have hh : A.outputProjectionEdge P b (A.stdE i g) = c := hg.symm ▸ he
      rw [A.projection_edge_std P b hA] at hh
      exact ⟨(i,⟨g,hh⟩),Subtype.ext hg⟩
  exact Equiv.ofBijective f ⟨hi,hs⟩

/-- Use the product indexing on the actual future-strip edges. -/
def futureEmbedding : (I × A.OldStripEdge P c) ↪ A.Edge where
  toFun p := A.stdE p.1 p.2.val
  inj' := A.future_edge_injective P b c hA hne

def futureHypergraph : ContactHypergraphData A.Vertex (I × A.OldStripEdge P c) PEmpty.{v+1} :=
  A.outputHypergraph.pullEdges (A.futureEmbedding P b c hA hne)

def futureTrain : ContactTrainData (I × A.OldStripEdge P c) m :=
  A.outputTrain.pullTrain (A.futureEmbedding P b c hA hne)

theorem future_carrier (i : I) (f : A.OldStripEdge P c) :
    (A.futureHypergraph P b c hA hne).edgeCarrier (i,f) =
      A.stdV i '' L.edgeCarrier f.val := by
  change A.outputHypergraph.edgeCarrier (A.stdE i f.val) = _
  exact A.output_carrier_std i (Sum.inr f.val)

theorem future_train_rel (μ : Fin (m+1)) (i : I) (f g : A.OldStripEdge P c) :
    (A.futureTrain P b c hA hne).parent μ (i,f) =
      (A.futureTrain P b c hA hne).parent μ (i,g) ↔
      S.parent μ f.val = S.parent μ g.val := by
  exact (A.outputTrain.pullTrain_rel (A.futureEmbedding P b c hA hne) μ (i,f) (i,g)).trans
    (A.outputTrain_std_rel μ i f.val g.val)

/-- Cross-standard intersections are actual vertices of the two
core copies projecting to the common base part. -/
theorem future_cross_trace (p : V → X) (hc : A.CoreOver P b p)
    (i j : I) (hij : i ≠ j) (e f : A.OldStripEdge P c) :
    (A.futureHypergraph P b c hA hne).edgeCarrier (i,e) ∩
      (A.futureHypergraph P b c hA hne).edgeCarrier (j,f) ⊆
        (A.coreV '' D.copyCarrier i) ∩ (A.coreV '' D.copyCarrier j) ∩
          (A.outputProjectionVertex P p ⁻¹' (base b ∩ base c)) := by
  rw [A.future_carrier P b c hA hne,A.future_carrier P b c hA hne]
  intro x hx
  obtain ⟨u,hu,he⟩ := hx.1
  obtain ⟨v,hv,hf⟩ := hx.2
  have hcore := contactGlued_shared A.vertexGlue A.vertex_inj i j hij x
    ⟨u,he⟩ ⟨v,hf⟩
  obtain ⟨y,hy⟩ := hcore
  have hi : A.vertexGlue i u = some y :=
    (contactStandardEmb_eq_core A.vertexGlue A.vertex_inj i u y).mp (he.trans hy.symm)
  have hj : A.vertexGlue j v = some y :=
    (contactStandardEmb_eq_core A.vertexGlue A.vertex_inj j v y).mp (hf.trans hy.symm)
  have hcopyi := (A.vertex_domain i y).mp ⟨u,hi⟩
  have hcopyj := (A.vertex_domain j y).mp ⟨v,hj⟩
  have hstrip := (hA.vertex_domain i u).mp ⟨y,hi⟩
  have hpb := P.strip_projects b hstrip
  have hpc : P.vertex u ∈ base c := by
    rw [← e.property,← P.edge_image]
    exact ⟨u,hu,rfl⟩
  refine ⟨⟨⟨y,hcopyi,hy⟩,⟨y,hcopyj,hy⟩⟩,?_⟩
  change A.outputProjectionVertex P p x ∈ base b ∩ base c
  rw [← he,A.projection_vertex_std P b p hc]
  exact ⟨hpb,hpc⟩

/-- The original first-level relation of the future strip in
each standard is exactly the one retained by the old refinement.
Construct the new refinement on the actual product edge labels. -/
def futureRefinement {d h : ℕ} (hm : m = h+1)
    (hd : 0 < d) (R : ContactTrainData (A.OldStripEdge P c) (d+h))
    (hret : ∀ e f, R.parent ⟨d,by omega⟩ e = R.parent ⟨d,by omega⟩ f ↔
      S.parent ⟨1,by omega⟩ e.val = S.parent ⟨1,by omega⟩ f.val) :
    ContactSplitRefinement (E := A.OldStripEdge P c) (Q := I) d h := by
  subst m
  exact {
    depth_pos := hd
    old := R
    coarse := A.futureTrain P b c hA hne
    boundary := fun i e f => (hret e f).trans
      (A.future_train_rel P b c hA hne ⟨1,by omega⟩ i e f).symm
  }

/-- Core-copy separators meet the allowed overlap in at most
one point. This is the only intersection property needed in the
new split-child girth argument. -/
theorem core_copy_overlap_subsingleton
    (p : V → X) (hc : A.CoreOver P b p)
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hD : D.bottomCut.ZeroPairwise)
    (i j : I) (hij : i ≠ j) :
    ((A.coreV '' D.copyCarrier i) ∩ (A.coreV '' D.copyCarrier j) ∩
      (A.outputProjectionVertex P p ⁻¹' (base b ∩ base c))).Subsingleton := by
  classical
  rintro x ⟨⟨⟨u,hu,rfl⟩,⟨u',hu',he⟩⟩,hx⟩
    y ⟨⟨⟨v,hv,rfl⟩,⟨v',hv',hf⟩⟩,hy⟩
  have heq := A.coreV.injective he
  have hfq := A.coreV.injective hf
  subst u'
  subst v'
  rcases hD (Sum.inl i) (Sum.inl j) (fun h => hij (Sum.inl.inj h)) with hs | ⟨e,_,_,he⟩
  · exact congrArg A.coreV (hs ⟨hu,hu'⟩ ⟨hv,hv'⟩)
  · have huE : u ∈ D.edgeCarrier e := he ▸ (show u ∈ D.copyCarrier i ∩ D.copyCarrier j from ⟨hu,hu'⟩)
    have hvE : v ∈ D.edgeCarrier e := he ▸ (show v ∈ D.copyCarrier i ∩ D.copyCarrier j from ⟨hv,hv'⟩)
    have heq : p u = p v := hbase b c (fun he => hne he.symm) hx hy
    exact congrArg A.coreV (hc.edge_inj e huE hvE heq)

end ContactTrainStrip
end StructuralRamsey.Girth
