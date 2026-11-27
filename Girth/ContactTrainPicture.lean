import Girth.ContactActualStepInvariant
import Girth.ContactSeedPicture
import Girth.ContactRefinementGirth
import Girth.ContactNonlinearSeedStep

/-! The finite picture state for the forest-boost and main train
iterations. All maps and labels refer to the same actual train.
The state keeps precisely the geometry needed for the next strip,
together with its order and actual target family. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B : Type v} {m : ℕ}
variable {D : ContactHypergraphData V E I} {T : ContactTrainData E m}
variable {base : B → Set X} [LinearOrder V] [LinearOrder X]

/-- A fixed-base picture with ordered actual designated embeddings.
The bottom condition can be small mixed forests (forest boost) or
the full system bound (main induction); the positive data are common. -/
structure ContactTrainPicture (D : ContactHypergraphData V E I)
    (T : ContactTrainData E m) (base : B → Set X)
    (allowed : Fin m → Set X) (q : Fin (m+1) → ℕ) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  finiteC : Finite Copy
  graph : ContactHypergraphData Vertex Edge Copy
  train : ContactTrainData Edge m
  projection : ContactBaseProjection graph base
  family : ContactDesignatedEmbeddings D T graph train
  order : LinearOrder Vertex
  projection_order : ∀ x y, order.lt x y → projection.vertex x ≤ projection.vertex y
  copy_order : ∀ i x y, x < y → order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  linear : ∀ e f, e ≠ f → (graph.edgeCarrier e ∩ graph.edgeCarrier f).Subsingleton
  covered : ∀ x, ∃ e, x ∈ graph.edgeCarrier e
  parameters : graph.Parameters train (fun j => projection.vertex ⁻¹' allowed j)
  positive : graph.PositiveBounds train q

namespace ContactTrainPicture
variable {allowed : Fin m → Set X} {q : Fin (m+1) → ℕ}
    (P : ContactTrainPicture D T base allowed q)

def focus : ContactFocusPicture E B where
  Edge := P.Edge
  Copy := P.Copy
  projection := P.projection.edge
  copy := fun i e => (P.family.emb i).edge e

def Forests (j : ℕ) : Prop := P.graph.bottomCut.ZeroSmallMixedForestsThrough j

def FullBounds : Prop := P.graph.SystemBounds P.train q

/-- All actual core data for the step at b, on precisely the
edge-covered restricted train. No output property is a field. -/
structure Core (b : B) where
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
  part : Vertex → X
  part_emb : ∀ i x, part ((family.emb i).vertex x) = P.projection.stripPart b x
  edge_image : ∀ e, part '' graph.edgeCarrier e = base b
  edge_inj : ∀ e, Set.InjOn part (graph.edgeCarrier e)
  order : LinearOrder Vertex
  copy_order : ∀ i (x y : P.projection.StripVertex b), P.order.lt x.val y.val →
    order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  linear : ∀ e f, e ≠ f → (graph.edgeCarrier e ∩ graph.edgeCarrier f).Subsingleton
  covered : ∀ x, ∃ e, x ∈ graph.edgeCarrier e
  parameters : graph.Parameters train (fun j => part ⁻¹' allowed j)
  positive : graph.PositiveBounds train q

namespace Core
variable {P} {b : B} (C : P.Core b)
    (hne : Nonempty (P.projection.StripEdge b))

noncomputable abbrev gluing := C.family.stripGluing hne

noncomputable def nextProjection :
    ContactBaseProjection (C.gluing hne).outputHypergraph base :=
  C.family.nextProjection hne C.part C.part_emb C.edge_image C.edge_inj

theorem finiteOutputVertex : Finite (C.gluing hne).Vertex := by
  letI : Finite C.Vertex := C.finiteV
  letI : Finite P.Vertex := P.finiteV
  letI : Finite C.Copy := C.finiteC
  exact Finite.of_injective
    (fun z : (C.gluing hne).Vertex => (z.val : C.Vertex ⊕ (C.Copy × P.Vertex)))
    Subtype.val_injective

theorem finiteOutputEdge : Finite (C.gluing hne).Edge := by
  letI : Finite C.Edge := C.finiteE
  letI : Finite P.Edge := P.finiteE
  letI : Finite C.Copy := C.finiteC
  exact Finite.of_injective
    (fun z : (C.gluing hne).Edge => (z.val : C.Edge ⊕ (C.Copy × P.Edge)))
    Subtype.val_injective

/-- The old part order is retained by the standards after
concatenating the parts of an arbitrary compatible glued order. -/
theorem exists_output_order :
    ∃ o : LinearOrder (C.gluing hne).Vertex,
      (∀ x y, o.lt x y → (C.nextProjection hne).vertex x ≤ (C.nextProjection hne).vertex y) ∧
      (∀ i x y, P.order.lt x y → o.lt ((C.gluing hne).stdV i x) ((C.gluing hne).stdV i y)) := by
  classical
  letI : Finite C.Vertex := C.finiteV
  letI : Finite P.Vertex := P.finiteV
  letI : Finite C.Copy := C.finiteC
  letI : Fintype C.Vertex := Fintype.ofFinite _
  letI : Fintype P.Vertex := Fintype.ofFinite _
  letI : LinearOrder C.Vertex := C.order
  letI : LinearOrder P.Vertex := P.order
  obtain ⟨o,_,hs⟩ := C.family.next_order hne C.copy_order
  let A := C.gluing hne
  let fi : Fintype A.Vertex := @Fintype.ofFinite _ (C.finiteOutputVertex hne)
  -- Encode the chosen glued order numerically before lifting the
  -- lexicographic order; do not synthesize another order on the quotient.
  let rank : A.Vertex → ℕ := @contactOrderRank A.Vertex fi o
  have hrank : ∀ x y : A.Vertex, o.lt x y → rank x < rank y :=
    fun x y h => @contactOrderRank_strict A.Vertex fi o x y h
  have hri : Function.Injective rank := by
    letI : LinearOrder A.Vertex := o
    exact (show StrictMono rank from fun {_ _} h => hrank _ _ h).injective
  let p := (C.nextProjection hne).vertex
  let key (x : A.Vertex) : X ×ₗ ℕ := toLex (p x,rank x)
  let o' : LinearOrder A.Vertex := LinearOrder.lift' key
    (fun x y h => hri (congrArg (fun z : X ×ₗ ℕ => (ofLex z).2) h))
  have hproj (i : C.Copy) (x : P.Vertex) :
      p (A.stdV i x) = P.projection.vertex x :=
    A.projection_vertex_std P.projection b C.part
      (C.family.stripGluing_coreOver hne C.part C.part_emb C.edge_image C.edge_inj) i x
  refine ⟨o',?_,?_⟩
  · intro x y h
    change key x < key y at h
    exact (Prod.Lex.toLex_lt_toLex'.mp h).1
  · intro i x y h
    change key (A.stdV i x) < key (A.stdV i y)
    apply Prod.Lex.toLex_lt_toLex'.mpr
    refine ⟨?_,fun _ => hrank _ _ (hs i x y h)⟩
    change p (A.stdV i x) ≤ p (A.stdV i y)
    rw [hproj,hproj]
    exact P.projection_order x y h

/-- Construct the next picture using the same actual gluing at
every cut. The standard embedding lifts the target family;
the order, projection and parameters are inherited simultaneously. -/
noncomputable def next
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ) :
    ContactTrainPicture D T base allowed q := by
  let A := C.gluing hne
  let hs := A.stripStrong_of_projection P.projection b (C.family.stripGluing_active hne) hbase
  letI : Finite C.Copy := C.finiteC
  letI : Finite P.Copy := P.finiteC
  let F := A.liftedFamily P.family hs C.family.copy_strong
  let ho := C.exists_output_order hne
  refine {
    Vertex := A.Vertex
    Edge := A.Edge
    Copy := C.Copy × P.Copy
    finiteV := C.finiteOutputVertex hne
    finiteE := C.finiteOutputEdge hne
    finiteC := inferInstance
    graph := A.outputHypergraph
    train := A.outputTrain
    projection := C.nextProjection hne
    family := F
    order := Classical.choose ho
    projection_order := (Classical.choose_spec ho).1
    copy_order := ?_
    linear := ?_
    covered := ?_
    parameters := C.family.next_parameters hne C.part C.part_emb C.edge_image C.edge_inj
      allowed C.parameters P.parameters q C.positive
    positive := A.preserves_positiveBounds q hq hs C.positive P.positive }
  · rintro ⟨i,j⟩ x y h
    exact (Classical.choose_spec ho).2 i _ _ (P.copy_order j x y h)
  · have hlin := A.nonlinear_output_linear (A.standardStrong_of_core hs C.family.copy_strong)
      C.family.copy_strong C.linear P.linear
    exact hlin
  · intro x
    rcases contactGlued_cover A.vertexGlue A.vertex_inj x with ⟨u,rfl⟩ | ⟨i,u,rfl⟩
    · obtain ⟨e,he⟩ := C.covered u
      refine ⟨A.coreE e,?_⟩
      change A.coreV u ∈ A.outputHypergraph.bottomCut.carrier (Sum.inr (A.coreE e))
      rw [A.output_carrier_core_edge]
      exact ⟨u,he,rfl⟩
    · obtain ⟨e,he⟩ := P.covered u
      refine ⟨A.stdE i e,?_⟩
      change A.stdV i u ∈ A.outputHypergraph.bottomCut.carrier (A.stdPieceLabel i (Sum.inr e))
      rw [A.output_carrier_std i (Sum.inr e)]
      exact ⟨u,he,rfl⟩

theorem next_forests
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    {j : ℕ} (hj : 2 ≤ j)
    (hP : P.Forests j)
    (hC : C.graph.bottomCut.ZeroSmallMixedForestsThrough (j-1))
    (hg : LabelledGirthGT C.graph.edgeCarrier j) :
    (C.next hne hbase hq).Forests j := by
  letI : Finite (C.gluing hne).Vertex := C.finiteOutputVertex hne
  letI : Fintype (C.gluing hne).Vertex := Fintype.ofFinite _
  exact (C.family.next_forestBoost hne hj q hq hbase C.linear hg hC hP C.positive P.positive).1

theorem next_fullBounds
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, μ.val < m → 2 ≤ q μ) (hm : 0 < m)
    (hP : P.FullBounds)
    (hC : C.graph.bottomCut.ZeroSmallMixedForestsThrough (q ⟨0,by omega⟩))
    (hsize : ∀ e, (C.graph.edgeCarrier e).Nontrivial) :
    (C.next hne hbase (fun μ _ h => hq μ h)).FullBounds :=
  C.family.next_systemBounds hne q hq hbase hC C.positive hP hsize hm

theorem next_focus
    (hbase : ∀ a b : B, a ≠ b → (base a ∩ base b).Subsingleton)
    (hq : ∀ μ, 0 < μ.val → μ.val < m → 2 ≤ q μ)
    {Color : Type v} (h : C.family.Arrow Color) :
    ContactFocusPicture.Step P.focus (C.next hne hbase hq).focus b Color :=
  C.family.focusStep P.family hne h

end Core
end ContactTrainPicture
end StructuralRamsey.Girth
