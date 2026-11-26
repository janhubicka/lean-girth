import Girth.ContactLinearSeedIteration

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

end ContactOrderedEdgeWord
end StructuralRamsey.Girth
