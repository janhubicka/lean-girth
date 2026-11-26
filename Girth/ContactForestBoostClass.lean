import Girth.ContactLocalCoreInput

/-! The class-wide induction in the forest-boost lemma. The lower
forest bound is an induction hypothesis on the entire class, not an
assumption about individual strips or their subsequent gluing.
The starting Ramsey pairs are the only external supply. -/

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

namespace ContactTrainPicture
variable [LinearOrder P] {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}
variable (A : ContactBoostInput P m allowed q)
variable {X B J : Type v} [LinearOrder X]
variable {H : ContactHypergraphData X B J}
variable (S : ContactPartiteEndpoints H P)
variable [LinearOrder A.Vertex]
variable (Q : ContactTrainPicture A.graph A.train H.edgeCarrier
  (fun j => S.part ⁻¹' allowed j) q)

/-- Every edge of the output has exactly one vertex over each
original part. The actual projection supplies both existence and
uniqueness, including edges not in a designated target copy. -/
noncomputable def outputEndpoints : ContactPartiteEndpoints Q.graph P := by
  classical
  have hex (e : Q.Edge) (p : P) : ∃ x, x ∈ Q.graph.edgeCarrier e ∧
      Q.projection.vertex x = S.endpoint (Q.projection.edge e) p := by
    have hmem := S.endpoint_mem (Q.projection.edge e) p
    rw [← Q.projection.edge_image e] at hmem
    exact hmem
  let f (e : Q.Edge) (p : P) := Classical.choose (hex e p)
  have hf (e : Q.Edge) (p : P) : f e p ∈ Q.graph.edgeCarrier e ∧
      Q.projection.vertex (f e p) = S.endpoint (Q.projection.edge e) p :=
    Classical.choose_spec (hex e p)
  refine {
    part := S.part ∘ Q.projection.vertex
    endpoint := f
    part_endpoint := ?_
    carrier_eq := ?_
    covered := Q.covered }
  · intro e p
    change S.part (Q.projection.vertex (f e p)) = p
    rw [(hf e p).2,S.part_endpoint]
  · intro e
    ext x
    constructor
    · intro hx
      have hmem : Q.projection.vertex x ∈ H.edgeCarrier (Q.projection.edge e) := by
        rw [← Q.projection.edge_image e]
        exact ⟨x,hx,rfl⟩
      let p := S.part (Q.projection.vertex x)
      exact ⟨p,Q.projection.edge_inj e (hf e p).1 hx
        ((hf e p).2.trans (S.endpoint_of_mem _ _ hmem))⟩
    · rintro ⟨p,rfl⟩
      exact (hf e p).1

/-- Pack an actual nonempty active strip back into the fixed
class. The positive wagon bounds and parameters are inherited. -/
noncomputable def boostStripInput (b : B) (hne : Nonempty (Q.projection.StripEdge b))
    (hmono : Monotone S.part) :
    ContactBoostInput P m allowed q := by
  letI : Finite Q.Vertex := Q.finiteV
  letI : Finite Q.Edge := Q.finiteE
  letI : LinearOrder Q.Vertex := Q.order
  let r := S.edgeLabelEquiv b
  have hr : Monotone r := fun _ _ h => hmono h
  have hparam (j : Fin m) (x : H.edgeCarrier b) :
      x.val ∈ S.part ⁻¹' allowed j ↔ r x ∈ allowed j := Iff.rfl
  exact {
    Vertex := Q.projection.StripVertex b
    Edge := Q.projection.StripEdge b
    Copy := PEmpty.{v+1}
    finiteV := inferInstance
    finiteE := inferInstance
    nonemptyE := hne
    graph := Q.projection.stripHypergraph b
    train := Q.projection.stripTrain Q.train b
    endpoints := Q.projection.relabelStripEndpoints b r
    order := inferInstance
    part_mono := fun x y h => Q.strip_original_order b r hr h
    linear := Q.projection.strip_linear b Q.linear
    parameters := Q.strip_original_parameters b r allowed hparam
    positiveWagons := fun μ hp ht => Q.strip_positive_wagonBounds b μ hp ht }

/-- Turn the lower-bound witness on that exact strip into its
actual gluing core. No preservation of the next picture is assumed. -/
noncomputable def boostCore (b : B) (hne : Nonempty (Q.projection.StripEdge b))
    (hmono : Monotone S.part) {Color : Type v}
    (W : (Q.boostStripInput A S b hne hmono).Witness Color) : Q.Core b := by
  let r := S.edgeLabelEquiv b
  let L : Q.LocalWitness b r := {
    Vertex := W.out.Vertex
    Edge := W.out.Edge
    Copy := W.out.Copy
    finiteV := W.out.finiteV
    finiteE := W.out.finiteE
    finiteC := W.finiteC
    graph := W.out.graph
    train := W.out.train
    family := W.family
    endpoints := W.out.endpoints
    emb_part := W.emb_part
    order := W.out.order
    emb_order := W.emb_order
    linear := W.out.linear
    positive := W.positive }
  exact L.toCore allowed (fun _ _ => Iff.rfl) W.out.parameters

/-- Output extraction as a member of the same fixed class. The
order is concatenated by the original part labels, not the seed
vertices. The arrow witnesses nonemptiness of the output edge type. -/
noncomputable def boostWitness {Color : Type v} [Nonempty Color]
    (horder : ∀ x y, x < y ↔ A.order.lt x y)
    (hpart : Q.PartPreserving A.endpoints.part S.part)
    (hArrow : Q.family.Arrow Color) : A.Witness Color := by
  let o := Q.originalPartOrder S.part
  let ep := Q.outputEndpoints A S
  have hE : Nonempty Q.Edge := by
    obtain ⟨i,_,_⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty Color))
    exact ⟨(Q.family.emb i).edge (Classical.choice A.nonemptyE)⟩
  have hm : Monotone A.endpoints.part := by
    intro x y h
    rcases lt_or_eq_of_le h with hlt | rfl
    · letI : LinearOrder A.Vertex := A.order
      exact A.part_mono x y ((horder x y).mp hlt).le
    · exact le_rfl
  refine {
    out := {
      Vertex := Q.Vertex
      Edge := Q.Edge
      Copy := Q.Copy
      finiteV := Q.finiteV
      finiteE := Q.finiteE
      nonemptyE := hE
      graph := Q.graph
      train := Q.train
      endpoints := ep
      order := o
      part_mono := ?_
      linear := Q.linear
      parameters := Q.parameters
      positiveWagons := fun μ hp ht => (Q.positive μ hp ht).g3 }
    finiteC := Q.finiteC
    family := Q.family
    emb_part := hpart
    emb_order := ?_
    positive := Q.positive
    arrow := hArrow }
  · intro x y h
    by_contra hn
    have ht : o.lt y x := ContactOrderedSeedStage.concatenate_part Q.order
      (S.part ∘ Q.projection.vertex) y x (lt_of_not_ge hn)
    letI : LinearOrder Q.Vertex := o
    exact (not_lt_of_ge h) ht
  · intro i x y h
    -- The picture source order is precisely the chosen input order in
    -- the application; keep its equality explicit instead of silently
    -- allowing a different source order.
    exact Q.originalPartOrder_copy_order hpart hm i x y ((horder x y).mpr h)

end ContactTrainPicture

namespace ContactBoostInput
variable [LinearOrder P] [Finite P] {m : ℕ} {allowed : Fin m → Set P} {q : Fin (m+1) → ℕ}

/-- One forest-boost step on the whole class, starting from any
smaller-bound supply on that class. The starting picture uses the
word seed, so there is no second application of the main theorem. -/
theorem boost_step {Color : Type v} [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    {j : ℕ} (hj : 2 ≤ j) (hjQ : j ≤ q 0)
    (hG : ∀ A : ContactBoostInput P m allowed q, LabelledGirthGT A.graph.edgeCarrier (q 0))
    (prev : ∀ A : ContactBoostInput P m allowed q,
      ∃ W : A.Witness Color, W.out.graph.bottomCut.ZeroSmallMixedForestsThrough (j-1))
    (A : ContactBoostInput P m allowed q) :
    ∃ W : A.Witness Color, W.out.graph.bottomCut.ZeroSmallMixedForestsThrough j := by
  classical
  letI : Finite A.Vertex := A.finiteV
  letI : Finite A.Edge := A.finiteE
  letI : LinearOrder A.Vertex := A.order
  let U := A.endpoints
  obtain ⟨N,hN,hword⟩ := U.exists_word_arrow (Color := Color)
  letI : Fintype N := hN
  let idx := Fintype.equivFin N
  letI : LinearOrder N := LinearOrder.lift' idx idx.injective
  letI : WellFoundedLT N := by
    change WellFounded (fun a b : N => idx a < idx b)
    exact InvImage.wf idx (inferInstance : WellFoundedLT (Fin (Fintype.card N)))
  let S := U.wordEndpoints N
  let seed := U.wordSeed N A.linear
  letI : Finite (U.WordVertex N) :=
    Finite.of_injective (fun x : U.WordVertex N => (x.val : P × (N → A.Vertex))) Subtype.val_injective
  letI : Finite (Combinatorics.Line A.Edge N) :=
    Finite.of_injective (fun l => l.idxFun) (fun _ _ he => Combinatorics.Line.ext he)
  letI : Fintype (N → A.Edge) := Fintype.ofFinite _
  letI : LinearOrder (U.WordVertex N) := U.wordOrder N
  have hSmono : Monotone S.part := fun x y h => U.wordPart_order N x y h
  have horder : ∀ i, StrictMono (seed.vertex i) :=
    fun i x y h => U.wordSeed_order N (fun x y h => A.part_mono x y h) i x y h
  have hpar : ∀ i, A.graph.Parameters A.train
      (fun j => seed.vertex i ⁻¹' (S.part ⁻¹' allowed j)) := by
    intro i
    exact A.parameters
  let Q := seed.initialPicture (T := A.train) hm (fun j => S.part ⁻¹' allowed j) q
    horder U.covered (A.all_cutLinear hq (hG A)) (A.all_wagonBounds (hG A)) hpar
  have hfull : Q.FullBounds := seed.initialPicture_fullBounds (T := A.train) hm
    (fun j => S.part ⁻¹' allowed j) q horder U.covered
    (A.all_cutLinear hq (hG A)) (A.all_wagonBounds (hG A)) hpar
  have hF : Q.Forests j := Q.forests_of_fullBounds hm hfull hjQ
  have hPart : Q.PartPreserving U.part S.part := by intro i x; rfl
  have hbase := U.word_linear N A.linear
  have hSupply : ContactTrainPicture.BoostCoreSupply (D := A.graph) (T := A.train)
      (base := (U.wordHypergraph N).edgeCarrier)
      (allowed := fun j => S.part ⁻¹' allowed j) (q := q) j Color := by
    intro R _ b hne
    let B := R.boostStripInput A S b hne hSmono
    obtain ⟨W,hW⟩ := prev B
    let C := R.boostCore A S b hne hSmono W
    refine ⟨C,hW,?_,W.arrow⟩
    rintro ⟨Z,hZ⟩
    exact hG W.out ⟨Z,hZ.trans hjQ⟩
  have hSeedArrow : ∀ ρ : (N → A.Edge) → Color, ∃ i : Q.Copy, ∃ c : Color,
      ∀ e : A.Edge, ρ (Q.projection.edge ((Q.family.emb i).edge e)) = c :=
    hword
  obtain ⟨R,hR,hRP,hRA⟩ := Q.boost_preservesPart hj hbase
    (fun μ _ h => hq μ h) hSupply hF hPart hSeedArrow
  exact ⟨R.boostWitness A S (fun _ _ => Iff.rfl) hRP hRA,hR⟩

/-- The full forest-boost lemma. Induction on j is genuinely
class-wide, so each local call in the next picture uses the
previous forest bound on a freshly constructed input. -/
theorem forestBoost {Color : Type v} [Finite Color] [Nonempty Color]
    (hm : 0 < m) (hq : ∀ μ, μ.val < m → 2 ≤ q μ)
    (hG : ∀ A : ContactBoostInput P m allowed q, LabelledGirthGT A.graph.edgeCarrier (q 0))
    (base : ∀ A : ContactBoostInput P m allowed q, Nonempty (A.Witness Color)) :
    ∀ n : ℕ, n+1 ≤ q 0 → ∀ A : ContactBoostInput P m allowed q,
      ∃ W : A.Witness Color, W.out.graph.bottomCut.ZeroSmallMixedForestsThrough (n+1) := by
  intro n
  induction n with
  | zero =>
    intro _ A
    obtain ⟨W⟩ := base A
    exact ⟨W,W.out.graph.bottomCut.zeroSmallMixedForests_one⟩
  | succ n ih =>
    intro hn A
    exact boost_step hm hq (by omega) hn hG (by
      intro B
      have h := ih (by omega) B
      convert h using 1 <;> omega) A

end ContactBoostInput
end StructuralRamsey.Girth
