import Girth.ContactCoverage
import Girth.ContactProfileRamseyApplications

/-! The covered output of the height-one theorem. Restriction is
performed only after the recursive construction, preserving the
actual ordered embeddings and all mixed forests at the requested
cutoff. No arbitrary deletion of nodes of a join tree is used. -/

namespace StructuralRamsey.Girth
universe v

namespace ContactProfileTrain
variable {P : Type v} [LinearOrder P] {m a : ℕ}
    {allowed : Fin m → Set P} {word : Fin a → P}
    {A : ContactProfileTrain P m a allowed word}
    {Color : Type v}

namespace Witness
variable (W : A.Witness Color)

/-- The vertices of every retained edge really survive restriction,
since the edge is contained in one designated copy. -/
theorem edge_vertices_used (e : W.out.graph.UsedEdge)
    (x : W.out.Vertex) (hx : x ∈ W.out.graph.edgeCarrier e.val) :
    ∃ j, x ∈ W.out.graph.copyCarrier j := by
  obtain ⟨j,hj⟩ := e.property
  rw [W.family.edge_eq] at hj
  obtain ⟨f,hf⟩ := hj
  refine ⟨j,?_⟩
  rw [W.family.vertex_eq]
  exact (W.family.emb j).vertex_range_of_edge f (hf.symm ▸ hx)

/-- A restriction of the output to its designated-copy union remains
a train with the exact original ordered edge profile and parameters. -/
noncomputable def restrictCovered [Nonempty Color] : A.Witness Color := by
  let H := W.out.graph
  letI : Finite W.out.Vertex := W.out.finiteV
  letI : Finite W.out.Edge := W.out.finiteE
  letI : LinearOrder W.out.Vertex := W.out.order
  letI : LinearOrder H.UsedVertex := inferInstance
  letI : Finite H.UsedVertex := Finite.of_injective H.usedVertexEmb H.usedVertexEmb.injective
  letI : Finite H.UsedEdge := Finite.of_injective H.usedEdgeEmb H.usedEdgeEmb.injective
  let f (e : H.UsedEdge) (i : Fin a) : H.UsedVertex :=
    ⟨W.out.enumeration e.val i, W.edge_vertices_used e _
      (by rw [W.out.carrier_eq]; exact ⟨i,rfl⟩)⟩
  have hf (e : H.UsedEdge) : StrictMono (f e) := fun i j h =>
    (W.out.enumeration e.val).strictMono h
  have hE : Nonempty H.UsedEdge := by
    obtain ⟨j,_,_⟩ := W.arrow (fun _ => Classical.choice (inferInstance : Nonempty Color))
    exact ⟨W.family.usedEdge j (Classical.choice A.nonemptyE)⟩
  let S := W.out.train.pullTrain H.usedEdgeEmb
  refine {
    out := {
      Vertex := H.UsedVertex
      Edge := H.UsedEdge
      Copy := W.out.Copy
      finiteV := inferInstance
      finiteE := inferInstance
      nonemptyE := hE
      graph := H.usedGraph
      train := S
      order := inferInstance
      part := fun x => W.out.part x.val
      enumeration := fun e => OrderEmbedding.ofStrictMono (f e) (hf e)
      carrier_eq := ?_
      part_eq := fun e i => W.out.part_eq e.val i
      part_mono := fun x y h => W.out.part_mono x.val y.val h
      covered := W.family.restrictCovered_noIsolated A.covered
      parameters := ?_ }
    finiteC := W.finiteC
    family := W.family.restrictCovered
    emb_part := W.emb_part
    emb_order := W.emb_order
    arrow := W.family.restrictCovered_arrow W.arrow }
  · intro e
    ext x
    change x.val ∈ H.edgeCarrier e.val ↔ x ∈ Set.range (f e)
    rw [W.out.carrier_eq]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i,Subtype.ext hi⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
  · intro j e f x he hx hy hn
    exact (W.out.train.pullTrain_rel H.usedEdgeEmb j.castSucc e f).mpr
      (W.out.parameters j e.val f.val x.val
        ((W.out.train.pullTrain_rel H.usedEdgeEmb j.succ e f).mp he) hx hy hn)

theorem restrictCovered_vertexCoverage [Nonempty Color] (x : (W.restrictCovered).out.Vertex) :
    ∃ i, x ∈ (W.restrictCovered).out.graph.copyCarrier i :=
  W.out.graph.usedGraph_vertexCoverage x

theorem restrictCovered_edgeCoverage [Nonempty Color] (e : (W.restrictCovered).out.Edge) :
    ∃ i, e ∈ (W.restrictCovered).out.graph.copyEdges i :=
  W.out.graph.usedGraph_edgeCoverage e

theorem restrictCovered_girth [Nonempty Color] {g : ℕ}
    (hg : LabelledGirthGT W.out.graph.edgeCarrier g) :
    LabelledGirthGT (W.restrictCovered).out.graph.edgeCarrier g :=
  W.out.graph.usedGraph_girth hg

theorem restrictCovered_smallForests [Nonempty Color] {g : ℕ}
    (hg : W.out.graph.bottomCut.ZeroSmallMixedForestsThrough g) :
    (W.restrictCovered).out.graph.bottomCut.ZeroSmallMixedForestsThrough g :=
  W.out.graph.usedGraph_smallForests hg

theorem restrictCovered_injective [Nonempty Color]
    (hi : Function.Injective W.out.graph.copyCarrier) :
    Function.Injective (W.restrictCovered).out.graph.copyCarrier :=
  W.out.graph.usedGraph_copyCarrier_injective hi

end Witness
end ContactProfileTrain

/-- The exact local-forest partite conclusion for edge-covered
inputs (indeed, for any ordered uniform part profile). Both vertices
and edges of the finite output belong to designated copies. -/
theorem contactProfileForestRamsey_covered
    {P : Type v} [LinearOrder P] [Finite P] {a : ℕ} (ha : 2 ≤ a)
    {allowed : Fin 1 → Set P} {word : Fin a → P}
    (A : ContactProfileTrain P 1 a allowed word)
    (g : ℕ) (hg : 2 ≤ g)
    (hG : LabelledGirthGT A.graph.edgeCarrier g)
    (Color : Type v) [Finite Color] [Nonempty Color] :
    ∃ W : A.Witness Color,
      LabelledGirthGT W.out.graph.edgeCarrier g ∧
      W.out.graph.bottomCut.ZeroSmallMixedForestsThrough g ∧
      Function.Injective W.out.graph.copyCarrier ∧
      (∀ x, ∃ i, x ∈ W.out.graph.copyCarrier i) ∧
      (∀ e, ∃ i, e ∈ W.out.graph.copyEdges i) := by
  obtain ⟨W,hW,hF,hI⟩ := contactProfileForestRamsey ha A g hg hG Color
  exact ⟨W.restrictCovered,W.restrictCovered_girth hW,W.restrictCovered_smallForests hF,
    W.restrictCovered_injective hI,W.restrictCovered_vertexCoverage,W.restrictCovered_edgeCoverage⟩

end StructuralRamsey.Girth
