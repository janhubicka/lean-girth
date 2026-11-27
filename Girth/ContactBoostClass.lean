import Girth.ContactPartPreservation

/-! Common finite ordered train input class for the class-wide mixed-forest
induction, and the word construction. This file is independent of the
local-core adapter and the induction on the mixed-forest bound. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P : Type v}

/-- Girth greater than two on a labelled family forces linearity
even when the carrier map was not assumed injective. -/
theorem contact_pairwise_of_labelledGirth (carrier : E → Set V) {q : ℕ}
    (hq : 2 ≤ q) (hg : LabelledGirthGT carrier q) :
    ∀ e f : E, e ≠ f → (carrier e ∩ carrier f).Subsingleton := by
  classical
  intro e f hef x hx y hy
  by_contra hxy
  let lab : Fin 2 → E := fun i => if i = 0 then e else f
  let vert : Fin 2 → V := fun i => if i = 0 then x else y
  have hl : Function.Injective lab := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [lab]
  have hv : Function.Injective vert := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [vert]
  let C : LabelledBergeCycle carrier := {
    length := 2
    hlength := le_rfl
    label := lab
    vertex := vert
    label_injective := hl
    vertex_injective := hv
    left_mem := by
      intro i
      fin_cases i
      · simpa [lab,vert] using hx.1
      · simpa [lab,vert] using hy.2
    right_mem := by
      intro i
      fin_cases i
      · simpa [lab,vert,cyclicSucc] using hx.2
      · simpa [lab,vert,cyclicSucc] using hy.1 }
  exact hg ⟨C,hq⟩

namespace ContactHypergraphData
variable (D : ContactHypergraphData V E I) {m : ℕ} (T : ContactTrainData E m)

/-- The bottom wagon labels are bijective to the edge labels. -/
theorem bottom_wagon_carrier (e : E) :
    (D.atCut (T.parent 0)).contactWagonCarrier (T.bottomEquiv e) =
      D.edgeCarrier e := by
  ext x
  constructor
  · rintro ⟨f,hf,hx⟩
    have he : f = e := T.bottom hf
    exact he ▸ hx
  · intro hx
    exact ⟨e,rfl,hx⟩

theorem bottom_wagon_girth {q : ℕ} (hg : LabelledGirthGT D.edgeCarrier q) :
    LabelledGirthGT (D.atCut (T.parent 0)).contactWagonCarrier q := by
  apply labelledGirthGT_of_injective_shrinking D.edgeCarrier
    (D.atCut (T.parent 0)).contactWagonCarrier
    T.bottomEquiv.symm T.bottomEquiv.symm.injective ?_ q hg
  intro p
  obtain ⟨e,rfl⟩ := T.bottomEquiv.surjective p
  rw [T.bottomEquiv.symm_apply_apply,D.bottom_wagon_carrier T]

end ContactHypergraphData

namespace ContactPartiteEndpoints
variable {D : ContactHypergraphData V E I} (A : ContactPartiteEndpoints D P)

/-- The actual bijection from the vertices of an edge to the part type. -/
def edgeLabelEquiv (e : E) : D.edgeCarrier e ≃ P where
  toFun x := A.part x.val
  invFun p := ⟨A.endpoint e p,A.endpoint_mem e p⟩
  left_inv x := Subtype.ext (A.endpoint_of_mem e x.val x.property)
  right_inv := A.part_endpoint e

def wordEndpoints (N : Type) : ContactPartiteEndpoints (A.wordHypergraph N) P where
  part := A.wordPart N
  endpoint := A.wordEnd N
  part_endpoint := fun _ _ => rfl
  carrier_eq := fun _ => rfl
  covered := A.word_covered N

def wordSeed (N : Type)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ContactSeed D (A.wordHypergraph N).edgeCarrier (Combinatorics.Line E N) where
  vertex := A.lineVertexEmb N
  edge := A.lineEdgeEmb N
  carrier_eq := A.line_carrier N
  strong := A.line_strong N hlin

theorem wordSeed_order [LinearOrder V] [LinearOrder P] (N : Type)
    [LinearOrder N] [WellFoundedLT N] (hmono : Monotone A.part)
    (l : Combinatorics.Line E N) (x y : V) (h : x < y) :
    (A.wordOrder N).lt (A.lineVertexEmb N l x) (A.lineVertexEmb N l y) := by
  by_cases he : A.part x = A.part y
  · exact A.line_order N l x y he h
  · have hlt := lt_of_le_of_ne (hmono h.le) he
    change (toLex (A.part x,toLex ((A.lineTuple N l x).2)) : P ×ₗ Lex (N → V)) <
      toLex (A.part y,toLex ((A.lineTuple N l y).2))
    exact Prod.Lex.left _ _ hlt

theorem wordPart_order [LinearOrder V] [LinearOrder P] (N : Type)
    [LinearOrder N] [WellFoundedLT N] (x y : A.WordVertex N)
    (h : (A.wordOrder N).le x y) : A.wordPart N x ≤ A.wordPart N y := by
  change (toLex (x.val.1,toLex x.val.2) : P ×ₗ Lex (N → V)) ≤
    toLex (y.val.1,toLex y.val.2) at h
  by_contra hn
  have hlt : (toLex (y.val.1,toLex y.val.2) : P ×ₗ Lex (N → V)) <
      toLex (x.val.1,toLex x.val.2) :=
    Prod.Lex.left _ _ (lt_of_not_ge hn)
  exact (not_lt_of_ge h) hlt

end ContactPartiteEndpoints

/-- The fixed class in the forest-boost lemma. The bottom girth
is intentionally NOT a field: the class-wide girth theorem is a
separate hypothesis. No copy-system condition is imposed on an input. -/
structure ContactBoostInput (P : Type v) [LinearOrder P] (m : ℕ)
    (allowed : Fin m → Set P) (q : Fin (m+1) → ℕ) where
  Vertex : Type v
  Edge : Type v
  Copy : Type v
  finiteV : Finite Vertex
  finiteE : Finite Edge
  nonemptyE : Nonempty Edge
  graph : ContactHypergraphData Vertex Edge Copy
  train : ContactTrainData Edge m
  endpoints : ContactPartiteEndpoints graph P
  order : LinearOrder Vertex
  part_mono : ∀ x y, order.le x y → endpoints.part x ≤ endpoints.part y
  linear : ∀ e f, e ≠ f → (graph.edgeCarrier e ∩ graph.edgeCarrier f).Subsingleton
  parameters : graph.Parameters train (fun j => endpoints.part ⁻¹' allowed j)
  positiveWagons : ∀ μ, 0 < μ.val → μ.val < m →
    LabelledGirthGT (graph.atCut (train.parent μ)).contactWagonCarrier (q μ)

namespace ContactBoostInput
variable [LinearOrder P] {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}
    (A : ContactBoostInput P m allowed q)

/-- The base witness property. The conclusion is stronger than an
abstract Ramsey arrow: the same ordered actual embeddings provide
the positive system bounds, the part map and the incidence labels. -/
structure Witness (Color : Type v) where
  out : ContactBoostInput P m allowed q
  finiteC : Finite out.Copy
  family : ContactDesignatedEmbeddings A.graph A.train out.graph out.train
  emb_part : ∀ i x, out.endpoints.part ((family.emb i).vertex x) = A.endpoints.part x
  emb_order : ∀ i x y, A.order.lt x y → out.order.lt ((family.emb i).vertex x) ((family.emb i).vertex y)
  positive : out.graph.PositiveBounds out.train q
  arrow : family.Arrow Color

/-- Proper wagon bounds follow from the class hypothesis at zero
and the positive bounds in the input. -/
theorem all_wagonBounds (hg : LabelledGirthGT A.graph.edgeCarrier (q 0)) :
    A.graph.WagonBounds A.train q := by
  intro μ hm
  by_cases hz : μ.val = 0
  · have he : μ = 0 := Fin.ext (by simpa using hz)
    rw [he]
    exact A.graph.bottom_wagon_girth A.train hg
  · exact A.positiveWagons μ (by omega) hm

theorem all_cutLinear (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (hg : LabelledGirthGT A.graph.edgeCarrier (q 0)) :
    ∀ μ, μ.val < m → (A.graph.atCut (A.train.parent μ)).ContactLinear := by
  intro μ hm
  exact ⟨A.linear,contact_pairwise_of_labelledGirth _ (hq μ hm) (A.all_wagonBounds hg μ hm)⟩

end ContactBoostInput

end StructuralRamsey.Girth
