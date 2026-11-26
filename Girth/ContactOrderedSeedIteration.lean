import Girth.ContactLinearSeedIteration
import Girth.ContactActualStepInvariant

/-! Compatible part orders for the actual nonlinear seed iteration.
First extend the core and all standard orders, then concatenate
the fixed base parts. The latter operation preserves each
standard order because it was already concatenated by the
same projection. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I X B P : Type v}
variable {D : ContactHypergraphData V E I} {base : B → Set X}
    [LinearOrder V] [LinearOrder X]

/-- The extra information carried through the seed construction.
The base is fixed, and part labels of the target and seed need
not be injective. -/
structure ContactOrderedSeedStage (D : ContactHypergraphData V E I)
    (base : B → Set X) (part : V → P) (label : X → P) where
  stage : ContactSeedStage D base
  order : LinearOrder stage.Vertex
  part_order : ∀ x y, stage.projection.vertex x < stage.projection.vertex y → order.lt x y
  emb_order : ∀ i x y, x < y → order.lt ((stage.emb i).vertex x) ((stage.emb i).vertex y)
  label_eq : ∀ i x, label (stage.projection.vertex ((stage.emb i).vertex x)) = part x

namespace ContactOrderedSeedStage
variable {part : V → P} {label : X → P} (A : ContactOrderedSeedStage D base part label)

/-- Concatenate the parts of any finite linearly ordered
picture without changing the order within each part. -/
noncomputable def concatenate {Y : Type v} (o : LinearOrder Y) (p : Y → X) : LinearOrder Y :=
  letI : LinearOrder Y := o
  LinearOrder.lift' (fun y => (toLex (p y,y) : X ×ₗ Y))
    (fun x y h => congrArg (fun z : X ×ₗ Y => (ofLex z).2) h)

theorem concatenate_part {Y : Type v} (o : LinearOrder Y) (p : Y → X)
    (x y : Y) (h : p x < p y) :
    (concatenate o p).lt x y := by
  letI : LinearOrder Y := o
  change (toLex (p x,x) : X ×ₗ Y) < toLex (p y,y)
  exact Prod.Lex.left _ _ h

theorem concatenate_within {Y : Type v} (o : LinearOrder Y) (p : Y → X)
    (x y : Y) (hp : p x = p y) (h : o.lt x y) :
    (concatenate o p).lt x y := by
  letI : LinearOrder Y := o
  change (toLex (p x,x) : X ×ₗ Y) < toLex (p y,y)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hp,h⟩)

/-- Projection cannot move backwards in a concatenated order. -/
theorem projection_mono (x y : A.stage.Vertex) (h : A.order.lt x y) :
    A.stage.projection.vertex x ≤ A.stage.projection.vertex y := by
  letI : LinearOrder A.stage.Vertex := A.order
  by_contra hn
  exact (lt_asymm h (A.part_order y x (lt_of_not_ge hn)))

/-- The actual word step has compatible finite orders.
The first variable coordinate proves within-part order
preservation of each combinatorial line. -/
noncomputable def next (b : B) (N : Type) [Fintype N]
    (hne : Nonempty (A.stage.projection.StripEdge b)) :
    ContactOrderedSeedStage D base part label := by
  classical
  let Q := A.stage
  letI : Finite Q.Vertex := Q.finiteV
  letI : Finite Q.Edge := Q.finiteE
  letI : Fintype Q.Vertex := Fintype.ofFinite _
  letI : LinearOrder Q.Vertex := A.order
  let idx := Fintype.equivFin N
  letI : LinearOrder N := LinearOrder.lift' idx idx.injective
  letI : WellFoundedLT N := ⟨InvImage.wf idx (inferInstance : WellFoundedLT (Fin (Fintype.card N))).wf⟩
  let W := Q.projection.stripEndpoints b
  let M := Q.wordCoreFamily b N
  let G := Q.wordGluing b N hne
  letI : Finite (Combinatorics.Line (Q.projection.StripEdge b) N) :=
    Finite.of_injective (fun l => l.idxFun) (fun _ _ h => Combinatorics.Line.ext h)
  letI : Fintype (W.WordVertex N) := Fintype.ofFinite _
  letI : LinearOrder (W.WordVertex N) := W.wordOrder N
  have hord : ∀ i (x y : Q.projection.StripVertex b), x.val < y.val →
      (M.emb i).vertex x < (M.emb i).vertex y := by
    intro i x y hxy
    have hmono := A.projection_mono x.val y.val hxy
    by_cases hEq : W.part x = W.part y
    · exact W.line_order N i x y hEq hxy
    · have hlt : W.part x < W.part y := by
        exact lt_of_le_of_ne hmono hEq
      change (W.wordOrder N).lt (W.lineVertexEmb N i x) (W.lineVertexEmb N i y)
      change (toLex (W.part x,toLex ((W.lineTuple N i x).2)) :
          (base b) ×ₗ Lex (N → Q.projection.StripVertex b)) <
        toLex (W.part y,toLex ((W.lineTuple N i y).2))
      exact Prod.Lex.left _ _ hlt
  obtain ⟨o,_,hstd⟩ := M.next_order hne hord
  let R := Q.next b N hne
  let o' := concatenate o R.projection.vertex
  refine {
    stage := R
    order := o'
    part_order := fun x y h => concatenate_part o R.projection.vertex x y h
    emb_order := ?_
    label_eq := ?_ }
  · rintro ⟨i,j⟩ x y h
    have hxy := A.emb_order j x y h
    have hle := A.projection_mono ((Q.emb j).vertex x) ((Q.emb j).vertex y) hxy
    by_cases he : Q.projection.vertex ((Q.emb j).vertex x) =
        Q.projection.vertex ((Q.emb j).vertex y)
    · apply concatenate_within
      · rw [Q.next_emb_vertex b N hne,Q.next_emb_vertex b N hne,he]
      · exact hstd i _ _ hxy
    · apply concatenate_part
      rw [Q.next_emb_vertex b N hne,Q.next_emb_vertex b N hne]
      exact lt_of_le_of_ne hle he
  · rintro ⟨i,j⟩ x
    rw [Q.next_emb_vertex b N hne]
    exact A.label_eq j x

theorem exists_next (b : B) {Color : Type v} [Finite Color] [Nonempty Color] :
    ∃ Q : ContactOrderedSeedStage D base part label,
      ContactFocusPicture.Step A.stage.focus Q.stage.focus b Color := by
  classical
  by_cases hne : Nonempty (A.stage.projection.StripEdge b)
  · letI : Finite A.stage.Edge := A.stage.finiteE
    obtain ⟨N,hN,hword⟩ :=
      (A.stage.projection.stripEndpoints b).exists_word_arrow (Color := Color)
    letI : Fintype N := hN
    exact ⟨A.next b N hne,A.stage.next_focus b N hne hword⟩
  · refine ⟨A,?_⟩
    intro χ
    refine ⟨Function.Embedding.refl _,id,fun _ => rfl,fun _ _ => rfl,
      Classical.choice (inferInstance : Nonempty Color),?_⟩
    intro e he
    exact (hne ⟨⟨e,he⟩⟩).elim

theorem exists_chain (l : List B) {Color : Type v} [Finite Color] [Nonempty Color] :
    ∃ Q : ContactOrderedSeedStage D base part label,
      ContactFocusPicture.Chain Color A.stage.focus Q.stage.focus l := by
  induction l with
  | nil => exact ⟨A,ContactFocusPicture.Chain.nil _⟩
  | cons b l ih =>
    obtain ⟨Q,hQ⟩ := ih
    obtain ⟨R,hR⟩ := Q.exists_next b (Color := Color)
    exact ⟨R,ContactFocusPicture.Chain.snoc hQ hR⟩

theorem exists_linear_seed [Fintype B] {Color : Type v} [Finite Color] [Nonempty Color]
    (hbase : ∀ ρ : B → Color, ∃ i : A.stage.Copy, ∃ c : Color,
      ∀ e, ρ (A.stage.projection.edge ((A.stage.emb i).edge e)) = c) :
    ∃ Q : ContactOrderedSeedStage D base part label,
      ∀ χ : Q.stage.Edge → Color, ∃ i : Q.stage.Copy, ∃ c : Color,
        ∀ e, χ ((Q.stage.emb i).edge e) = c := by
  classical
  let l := (Finset.univ : Finset B).toList
  obtain ⟨Q,hQ⟩ := A.exists_chain l (Color := Color)
  refine ⟨Q,hQ.arrow_of_base ?_ hbase⟩
  intro b
  simp [l]

end ContactOrderedSeedStage

namespace ContactOrderedEdgeWord
variable [LinearOrder P] {a : ℕ} (A : ContactOrderedEdgeWord D P a)

/-- Order the raw seed first by position, then by the label. -/
noncomputable def rawOrder (N : ℕ) : LinearOrder (A.SeedVertex N) :=
  LinearOrder.lift' (fun x => (toLex x : Fin N ×ₗ P))
    (fun x y h => congrArg ofLex h)

/-- The initial disjoint picture is ordered by the projected
base vertex and an arbitrary injective tie-breaker. Its actual
target embeddings preserve the source order. -/
noncomputable def orderedRawStage (N : ℕ) [Finite V] [Finite E] [Finite P]
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e))
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    letI : LinearOrder (A.SeedVertex N) := A.rawOrder N
    ContactOrderedSeedStage D (A.seedCarrier N) A.part Prod.snd := by
  classical
  letI : LinearOrder (A.SeedVertex N) := A.rawOrder N
  let Q := A.rawStage N hinj hlin
  letI : Finite Q.Vertex := Q.finiteV
  letI : Fintype Q.Vertex := Fintype.ofFinite _
  let tie := Fintype.equivFin Q.Vertex
  let o : LinearOrder Q.Vertex := LinearOrder.lift' tie tie.injective
  let o' := ContactOrderedSeedStage.concatenate o Q.projection.vertex
  refine {
    stage := Q
    order := o'
    part_order := fun x y h => ContactOrderedSeedStage.concatenate_part o Q.projection.vertex x y h
    emb_order := ?_
    label_eq := fun _ _ => rfl }
  intro j x y h
  apply ContactOrderedSeedStage.concatenate_part
  change (toLex (j x,A.part x) : Fin N ×ₗ P) < toLex (j y,A.part y)
  exact Prod.Lex.left _ _ (j.strictMono h)


/-- The final seed, with a finite ordered hypergraph, the common
part word, and actual strongly induced order/part-preserving
embeddings. The arrow is a theorem about these same embeddings. -/
structure LinearSeedResult (A : ContactOrderedEdgeWord D P a) (Color : Type v) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  finiteC : Finite Copy
  order : LinearOrder Vertex
  graph : ContactHypergraphData Vertex Edge PEmpty.{v+1}
  train : ContactTrainData Edge 1
  part : Vertex → P
  enumeration : letI : LinearOrder Vertex := order
    Edge → Fin a ↪o Vertex
  carrier_eq : ∀ e, graph.edgeCarrier e = Set.range (enumeration e)
  part_eq : ∀ e i, part (enumeration e i) = A.word i
  emb : Copy → ContactTrainEmbedding D (contactHeightOne E) graph train
  emb_order : ∀ j x y, x < y → order.lt ((emb j).vertex x) ((emb j).vertex y)
  emb_part : ∀ j x, part ((emb j).vertex x) = A.part x
  linear : ∀ e f, e ≠ f → (graph.edgeCarrier e ∩ graph.edgeCarrier f).Subsingleton
  arrow : ∀ χ : Edge → Color, ∃ j : Copy, ∃ c : Color, ∀ e, χ ((emb j).edge e) = c

/-- Every edge of the final picture is the unique lift of its
base edge. Lifting its increasing tuple gives precisely the
required ordered enumeration of that edge. -/
theorem exists_ordered_linear_seed [Fintype V] [Finite E] [Finite P]
    {Color : Type v} [Fintype Color] [Nonempty Color] [Nonempty E]
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e))
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    Nonempty (A.LinearSeedResult Color) := by
  classical
  obtain ⟨N,hN⟩ := A.exists_raw_seed_arrow (Color := Color) hinj
  letI : LinearOrder (A.SeedVertex N) := A.rawOrder N
  letI : Fintype (A.SeedEdge N) := Fintype.ofFinite _
  let Q₀ := A.orderedRawStage N hinj hlin
  obtain ⟨Q,hQ⟩ := Q₀.exists_linear_seed (Color := Color) hN
  let S := Q.stage
  letI : LinearOrder S.Vertex := Q.order
  let basePoint (e : S.Edge) (i : Fin a) : A.SeedVertex N :=
    (S.projection.edge e i,A.word i)
  have hex (e : S.Edge) (i : Fin a) :
      ∃ x, x ∈ S.graph.edgeCarrier e ∧ S.projection.vertex x = basePoint e i := by
    have hx : basePoint e i ∈ A.seedCarrier N (S.projection.edge e) := ⟨i,rfl⟩
    rw [← S.projection.edge_image e] at hx
    exact hx
  let lift (e : S.Edge) (i : Fin a) := Classical.choose (hex e i)
  have hlift (e : S.Edge) (i : Fin a) :
      lift e i ∈ S.graph.edgeCarrier e ∧ S.projection.vertex (lift e i) = basePoint e i :=
    Classical.choose_spec (hex e i)
  have hmono (e : S.Edge) : StrictMono (lift e) := by
    intro i j hij
    apply Q.part_order
    rw [(hlift e i).2,(hlift e j).2]
    change (toLex (S.projection.edge e i,A.word i) : Fin N ×ₗ P) <
      toLex (S.projection.edge e j,A.word j)
    exact Prod.Lex.left _ _ ((S.projection.edge e).strictMono hij)
  refine ⟨{
    Vertex := S.Vertex
    Edge := S.Edge
    Copy := S.Copy
    finiteV := S.finiteV
    finiteE := S.finiteE
    finiteC := S.finiteC
    order := Q.order
    graph := S.graph
    train := S.train
    part := fun x => (S.projection.vertex x).2
    enumeration := fun e => OrderEmbedding.ofStrictMono (lift e) (hmono e)
    carrier_eq := ?_
    part_eq := ?_
    emb := S.emb
    emb_order := Q.emb_order
    emb_part := Q.label_eq
    linear := S.linear
    arrow := hQ }⟩
  · intro e
    ext x
    constructor
    · intro hx
      have hm : S.projection.vertex x ∈ A.seedCarrier N (S.projection.edge e) := by
        rw [← S.projection.edge_image e]
        exact ⟨x,hx,rfl⟩
      obtain ⟨i,hi⟩ := hm
      exact ⟨i,S.projection.edge_inj e (hlift e i).1 hx ((hlift e i).2.trans hi)⟩
    · rintro ⟨i,rfl⟩
      exact (hlift e i).1
  · intro e i
    exact congrArg Prod.snd (hlift e i).2

end ContactOrderedEdgeWord
end StructuralRamsey.Girth
