import Girth.ContactTrainData
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Order.PiLex
import Mathlib.Order.Prod.Lex.Basic

/-! The word base for an a-partite linear hypergraph. The
endpoints of an edge are indexed by its parts. The actual new
edges are words in the old edge alphabet, and every vertex is
covered by a word edge. Combinatorial lines give actual
strongly induced embeddings. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I A : Type v}

structure ContactPartiteEndpoints (D : ContactHypergraphData V E I) (A : Type v) where
  part : V → A
  endpoint : E → A → V
  part_endpoint : ∀ e a, part (endpoint e a) = a
  carrier_eq : ∀ e, D.edgeCarrier e = Set.range (endpoint e)
  covered : ∀ x, ∃ e, x ∈ D.edgeCarrier e

namespace ContactPartiteEndpoints
variable {D : ContactHypergraphData V E I} (P : ContactPartiteEndpoints D A)

theorem endpoint_mem (e : E) (a : A) :
    P.endpoint e a ∈ D.edgeCarrier e := by
  rw [P.carrier_eq]
  exact ⟨a,rfl⟩

theorem endpoint_inj (e : E) : Function.Injective (P.endpoint e) := by
  intro a b h
  exact (P.part_endpoint e a).symm.trans
    ((congrArg P.part h).trans (P.part_endpoint e b))

theorem endpoint_of_mem (e : E) (x : V) (hx : x ∈ D.edgeCarrier e) :
    P.endpoint e (P.part x) = x := by
  rw [P.carrier_eq] at hx
  obtain ⟨a,rfl⟩ := hx
  rw [P.part_endpoint]

theorem edge_eq_of_two_endpoints
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (e f : E) (a b : A) (hne : a ≠ b)
    (ha : P.endpoint e a = P.endpoint f a)
    (hb : P.endpoint e b = P.endpoint f b) : e = f := by
  by_contra hef
  apply hne
  apply P.endpoint_inj e
  exact hlin e f hef
    ⟨P.endpoint_mem e a,ha.symm ▸ P.endpoint_mem f a⟩
    ⟨P.endpoint_mem e b,hb.symm ▸ P.endpoint_mem f b⟩

variable (N : Type)

/-- A vertex of the word hypergraph is a part and an endpoint
tuple of some actual word edge. No isolated vertices are added. -/
def wordTuple (w : N → E) (a : A) : A × (N → V) :=
  (a,fun i => P.endpoint (w i) a)

def WordVertex := Set.range (fun p : (N → E) × A => P.wordTuple N p.1 p.2)

def wordEnd (w : N → E) (a : A) : P.WordVertex N :=
  ⟨P.wordTuple N w a,⟨(w,a),rfl⟩⟩

def wordPart (x : P.WordVertex N) : A := x.val.1

def wordCarrier (w : N → E) : Set (P.WordVertex N) := Set.range (P.wordEnd N w)

theorem wordEnd_inj (w : N → E) : Function.Injective (P.wordEnd N w) := by
  intro a b he
  exact congrArg (fun z : P.WordVertex N => z.val.1) he

theorem word_linear
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ∀ w w' : N → E, w ≠ w' →
      (P.wordCarrier N w ∩ P.wordCarrier N w').Subsingleton := by
  intro w w' hne x hx y hy
  obtain ⟨a,rfl⟩ := hx.1
  obtain ⟨b,hb⟩ := hx.2
  obtain ⟨c,rfl⟩ := hy.1
  obtain ⟨d,hd⟩ := hy.2
  have hab : b = a := congrArg (fun z : P.WordVertex N => z.val.1) hb
  have hcd : d = c := congrArg (fun z : P.WordVertex N => z.val.1) hd
  subst b
  subst d
  by_cases hac : a = c
  · rw [hac]
  · apply False.elim
    apply hne
    funext i
    have ha : P.endpoint (w' i) a = P.endpoint (w i) a :=
      congrArg (fun z : P.WordVertex N => z.val.2 i) hb
    have hc : P.endpoint (w' i) c = P.endpoint (w i) c :=
      congrArg (fun z : P.WordVertex N => z.val.2 i) hd
    exact P.edge_eq_of_two_endpoints hlin _ _ a c hac ha.symm hc.symm

theorem word_intersection_part
    (w w' : N → E) (hne : w ≠ w') (x : P.WordVertex N)
    (hx : x ∈ P.wordCarrier N w ∩ P.wordCarrier N w') :
    ∃ e f : E, e ≠ f ∧
      P.endpoint e (P.wordPart N x) = P.endpoint f (P.wordPart N x) := by
  classical
  have h : ∃ i, w i ≠ w' i := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i,hi⟩
  obtain ⟨i,hi⟩ := h
  obtain ⟨a,ha⟩ := hx.1
  obtain ⟨b,hb⟩ := hx.2
  have ha' : a = P.wordPart N x := congrArg (P.wordPart N) ha
  have hb' : b = P.wordPart N x := congrArg (P.wordPart N) hb
  have he := congrArg (fun z : P.WordVertex N => z.val.2 i) (ha.trans hb.symm)
  exact ⟨w i,w' i,hi,by simpa only [ha',hb'] using he⟩

def lineTuple (l : Combinatorics.Line E N) (x : V) : A × (N → V) :=
  (P.part x,fun i => (l.idxFun i).elim x (fun e => P.endpoint e (P.part x)))

theorem lineTuple_endpoint (l : Combinatorics.Line E N) (e : E) (a : A) :
    P.lineTuple N l (P.endpoint e a) = P.wordTuple N (l e) a := by
  apply Prod.ext
  · exact P.part_endpoint e a
  · funext i
    change (l.idxFun i).elim (P.endpoint e a)
      (fun f => P.endpoint f (P.part (P.endpoint e a))) = P.endpoint (l e i) a
    rw [P.part_endpoint]
    cases h : l.idxFun i <;> simp [h,Combinatorics.Line.coe_apply]

def lineVertex (l : Combinatorics.Line E N) : V → P.WordVertex N :=
  fun x => ⟨P.lineTuple N l x,by
    obtain ⟨e,he⟩ := P.covered x
    refine ⟨(l e,P.part x),?_⟩
    have h := P.lineTuple_endpoint N l e (P.part x)
    rw [P.endpoint_of_mem e x he] at h
    exact h.symm⟩

theorem lineVertex_inj (l : Combinatorics.Line E N) :
    Function.Injective (P.lineVertex N l) := by
  intro x y he
  obtain ⟨i,hi⟩ := l.proper
  have h := congrArg (fun z : P.WordVertex N => z.val.2 i) he
  change (l.idxFun i).elim x _ = (l.idxFun i).elim y _ at h
  simpa only [hi,Option.elim] using h

def lineVertexEmb (l : Combinatorics.Line E N) : V ↪ P.WordVertex N :=
  ⟨P.lineVertex N l,P.lineVertex_inj N l⟩

def lineEdgeEmb (_P : ContactPartiteEndpoints D A) (l : Combinatorics.Line E N) : E ↪ (N → E) where
  toFun := l
  inj' := by
    intro e f he
    obtain ⟨i,hi⟩ := l.proper
    have h := congrFun he i
    simpa [Combinatorics.Line.coe_apply,hi] using h

theorem line_vertex_endpoint (l : Combinatorics.Line E N) (e : E) (a : A) :
    P.lineVertexEmb N l (P.endpoint e a) = P.wordEnd N (l e) a :=
  Subtype.ext (P.lineTuple_endpoint N l e a)

theorem line_carrier (l : Combinatorics.Line E N) (e : E) :
    P.wordCarrier N (P.lineEdgeEmb N l e) =
      P.lineVertexEmb N l '' D.edgeCarrier e := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨P.endpoint e a,P.endpoint_mem e a,P.line_vertex_endpoint N l e a⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨P.part u,by rw [← P.line_vertex_endpoint,P.endpoint_of_mem e u hu]⟩

/-- Strong inducedness of a line. Two endpoints in distinct
parts fix every fixed-coordinate letter; at all variable
coordinates they fix the same letter by old linearity. -/
theorem line_strong (hlin : ∀ e f : E, e ≠ f →
    (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (l : Combinatorics.Line E N) (w : N → E)
    (hn : (P.wordCarrier N w ∩ Set.range (P.lineVertexEmb N l)).Nontrivial) :
    w ∈ Set.range (P.lineEdgeEmb N l) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := hn
  obtain ⟨a,ha⟩ := hx.1
  obtain ⟨b,hb⟩ := hy.1
  obtain ⟨u,hu⟩ := hx.2
  obtain ⟨v,hv⟩ := hy.2
  have hab : a ≠ b := by
    intro he
    exact hxy (ha.symm.trans ((congrArg (P.wordEnd N w) he).trans hb))
  have hau : P.part u = a := congrArg (P.wordPart N) (hu.trans ha.symm)
  have hbv : P.part v = b := congrArg (P.wordPart N) (hv.trans hb.symm)
  have hU (i : N) : P.endpoint (w i) a =
      (l.idxFun i).elim u (fun e => P.endpoint e a) := by
    have h := congrArg (fun z : P.WordVertex N => z.val.2 i) (ha.trans hu.symm)
    change P.endpoint (w i) a =
      (l.idxFun i).elim u (fun e => P.endpoint e (P.part u)) at h
    rw [hau] at h
    exact h
  have hV (i : N) : P.endpoint (w i) b =
      (l.idxFun i).elim v (fun e => P.endpoint e b) := by
    have h := congrArg (fun z : P.WordVertex N => z.val.2 i) (hb.trans hv.symm)
    change P.endpoint (w i) b =
      (l.idxFun i).elim v (fun e => P.endpoint e (P.part v)) at h
    rw [hbv] at h
    exact h
  obtain ⟨k,hk⟩ := l.proper
  refine ⟨w k,?_⟩
  funext i
  cases hi : l.idxFun i with
  | none =>
    have ha' : P.endpoint (w i) a = P.endpoint (w k) a := by
      exact (by simpa [hi] using hU i : P.endpoint (w i) a = u).trans
        (by simpa [hk] using (hU k).symm)
    have hb' : P.endpoint (w i) b = P.endpoint (w k) b := by
      exact (by simpa [hi] using hV i : P.endpoint (w i) b = v).trans
        (by simpa [hk] using (hV k).symm)
    have he := P.edge_eq_of_two_endpoints hlin _ _ a b hab ha' hb'
    simpa [Combinatorics.Line.coe_apply,hi] using he.symm
  | some e =>
    have ha' : P.endpoint (w i) a = P.endpoint e a := by simpa [hi] using hU i
    have hb' : P.endpoint (w i) b = P.endpoint e b := by simpa [hi] using hV i
    have he := P.edge_eq_of_two_endpoints hlin _ _ a b hab ha' hb'
    simpa [Combinatorics.Line.coe_apply,hi] using he.symm

def wordHypergraph : ContactHypergraphData (P.WordVertex N) (N → E) (Combinatorics.Line E N) where
  edgeCarrier := P.wordCarrier N
  copyCarrier := fun l => Set.range (P.lineVertexEmb N l)
  copyEdges := fun l => Set.range (P.lineEdgeEmb N l)

theorem word_covered (x : P.WordVertex N) :
    ∃ w : N → E, x ∈ (P.wordHypergraph N).edgeCarrier w := by
  obtain ⟨⟨w,a⟩,ha⟩ := x.property
  exact ⟨w,a,Subtype.ext ha⟩

/-- The exact Ramsey arrow of the word construction is Mathlib's
proved Hales--Jewett theorem, not a Ramsey oracle. -/
theorem exists_word_arrow [Finite E] {Color : Type v} [Finite Color] :
    ∃ (N : Type) (_ : Fintype N),
      ∀ χ : (N → E) → Color,
        ∃ l : Combinatorics.Line E N, ∃ c : Color,
          ∀ e, χ (P.lineEdgeEmb N l e) = c := by
  obtain ⟨N,hN,h⟩ := Combinatorics.Line.exists_mono_in_high_dimension E Color
  refine ⟨N,hN,?_⟩
  intro χ
  obtain ⟨l,c,hc⟩ := h χ
  exact ⟨l,c,hc⟩


theorem line_part (l : Combinatorics.Line E N) (x : V) :
    P.wordPart N (P.lineVertexEmb N l x) = P.part x := rfl

/-- A fixed coordinate of a line determines the corresponding
endpoint of every vertex in the image of the line. -/
theorem line_fixed_coordinate (l : Combinatorics.Line E N) (i : N) (e : E)
    (hi : l.idxFun i = some e) (x : P.WordVertex N)
    (hx : x ∈ Set.range (P.lineVertexEmb N l)) :
    x.val.2 i = P.endpoint e (P.wordPart N x) := by
  obtain ⟨u,rfl⟩ := hx
  change (l.idxFun i).elim u (fun f => P.endpoint f (P.part u)) =
    P.endpoint e (P.part u)
  rw [hi]
  rfl

/-- If a variable coordinate of one line is fixed in another
line, their entire intersection is contained in one edge of the
first line. -/
theorem line_intersection_subset_edge (l k : Combinatorics.Line E N)
    (i : N) (e : E) (hl : l.idxFun i = none) (hk : k.idxFun i = some e) :
    Set.range (P.lineVertexEmb N l) ∩ Set.range (P.lineVertexEmb N k) ⊆
      P.wordCarrier N (P.lineEdgeEmb N l e) := by
  rintro x ⟨⟨u,rfl⟩,hu⟩
  have h := P.line_fixed_coordinate N k i e hk (P.lineVertexEmb N l u) hu
  change (l.idxFun i).elim u _ = P.endpoint e (P.part u) at h
  rw [hl] at h
  have he : u = P.endpoint e (P.part u) := h
  rw [P.line_carrier]
  exact ⟨u,he.symm ▸ P.endpoint_mem e (P.part u),rfl⟩

/-- Two lines which share vertices in different parts have a
common edge as their entire intersection. Distinct lines with
the same variable pattern but different fixed letters cannot
share two parts, by old edge linearity. -/
theorem line_pair_intersection
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (l k : Combinatorics.Line E N) (hne : l ≠ k)
    (x y : P.WordVertex N)
    (hx : x ∈ Set.range (P.lineVertexEmb N l) ∩ Set.range (P.lineVertexEmb N k))
    (hy : y ∈ Set.range (P.lineVertexEmb N l) ∩ Set.range (P.lineVertexEmb N k))
    (hparts : P.wordPart N x ≠ P.wordPart N y) :
    ∃ w : N → E, w ∈ Set.range (P.lineEdgeEmb N l) ∧
      w ∈ Set.range (P.lineEdgeEmb N k) ∧
      Set.range (P.lineVertexEmb N l) ∩ Set.range (P.lineVertexEmb N k) =
        P.wordCarrier N w := by
  classical
  have hd : ∃ i, l.idxFun i ≠ k.idxFun i := by
    by_contra h
    apply hne
    apply Combinatorics.Line.ext
    funext i
    by_contra hi
    exact h ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hd
  have hxy : x ≠ y := fun he => hparts (congrArg (P.wordPart N) he)
  have aux (u v : Combinatorics.Line E N) (e : E)
      (hu : u.idxFun i = none) (hv : v.idxFun i = some e)
      (hx : x ∈ Set.range (P.lineVertexEmb N u) ∩ Set.range (P.lineVertexEmb N v))
      (hy : y ∈ Set.range (P.lineVertexEmb N u) ∩ Set.range (P.lineVertexEmb N v)) :
      ∃ w : N → E, w ∈ Set.range (P.lineEdgeEmb N u) ∧
        w ∈ Set.range (P.lineEdgeEmb N v) ∧
        Set.range (P.lineVertexEmb N u) ∩ Set.range (P.lineVertexEmb N v) =
          P.wordCarrier N w := by
    let w := P.lineEdgeEmb N u e
    have hsub := P.line_intersection_subset_edge N u v i e hu hv
    obtain ⟨f,hf⟩ := P.line_strong N hlin v w
      ⟨x,⟨hsub hx,hx.2⟩,y,⟨hsub hy,hy.2⟩,hxy⟩
    refine ⟨w,⟨e,rfl⟩,⟨f,hf⟩,Set.Subset.antisymm hsub ?_⟩
    intro z hz
    have hu' : z ∈ Set.range (P.lineVertexEmb N u) := by
      change z ∈ P.wordCarrier N (P.lineEdgeEmb N u e) at hz
      rw [P.line_carrier] at hz
      obtain ⟨a,_,he⟩ := hz
      exact ⟨a,he⟩
    have hv' : z ∈ Set.range (P.lineVertexEmb N v) := by
      rw [← hf,P.line_carrier] at hz
      obtain ⟨a,_,he⟩ := hz
      exact ⟨a,he⟩
    exact ⟨hu',hv'⟩
  cases hl : l.idxFun i with
  | none =>
    cases hk : k.idxFun i with
    | none => exact (hi (hl.trans hk.symm)).elim
    | some e => exact aux l k e hl hk hx hy
  | some e =>
    cases hk : k.idxFun i with
    | none =>
      obtain ⟨w,hw,hw',he⟩ := aux k l e hk hl ⟨hx.2,hx.1⟩ ⟨hy.2,hy.1⟩
      exact ⟨w,hw',hw,(Set.inter_comm _ _).trans he⟩
    | some f =>
      have heq := P.edge_eq_of_two_endpoints hlin e f
        (P.wordPart N x) (P.wordPart N y) hparts
        ((P.line_fixed_coordinate N l i e hl x hx.1).symm.trans
          (P.line_fixed_coordinate N k i f hk x hx.2))
        ((P.line_fixed_coordinate N l i e hl y hy.1).symm.trans
          (P.line_fixed_coordinate N k i f hk y hy.2))
      exact (hi (hl.trans ((congrArg some heq).trans hk.symm))).elim

/-- The word order is lexicographic within each part.
The first variable coordinate witnesses strict order preservation
for every line, and all earlier fixed coordinates agree. -/
noncomputable def wordOrder [LinearOrder A] [LinearOrder V]
    [LinearOrder N] [WellFoundedLT N] : LinearOrder (P.WordVertex N) :=
  LinearOrder.lift'
    (fun z : P.WordVertex N => (toLex (z.val.1,toLex z.val.2) : A ×ₗ Lex (N → V)))
    (fun x y h => Subtype.ext (Prod.ext
      (congrArg (fun z : A ×ₗ Lex (N → V) => (ofLex z).1) h)
      (congrArg (fun z : A ×ₗ Lex (N → V) => ofLex ((ofLex z).2)) h)))

theorem line_order [LinearOrder A] [LinearOrder V] [LinearOrder N] [WellFoundedLT N]
    (l : Combinatorics.Line E N) (u w : V)
    (hpart : P.part u = P.part w) (h : u < w) :
    (P.wordOrder N).lt (P.lineVertexEmb N l u) (P.lineVertexEmb N l w) := by
  classical
  let S : Set N := {i | l.idxFun i = none}
  have hS : S.Nonempty := l.proper
  obtain ⟨i,hi,hmin⟩ := (inferInstance : WellFoundedLT N).wf.has_min S hS
  change (toLex (P.part u,toLex ((P.lineTuple N l u).2)) : A ×ₗ Lex (N → V)) <
    toLex (P.part w,toLex ((P.lineTuple N l w).2))
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hpart,?_⟩
  change ∃ i : N, (∀ j : N, j < i → (P.lineTuple N l u).2 j =
    (P.lineTuple N l w).2 j) ∧ (P.lineTuple N l u).2 i < (P.lineTuple N l w).2 i
  refine ⟨i,?_,?_⟩
  · intro j hj
    have hn : l.idxFun j ≠ none := fun he => hmin j he hj
    cases he : l.idxFun j with
    | none => exact (hn he).elim
    | some e => simp [lineTuple,he,hpart]
  · change l.idxFun i = none at hi
    simpa [lineTuple,hi] using h

end ContactPartiteEndpoints
end StructuralRamsey.Girth
