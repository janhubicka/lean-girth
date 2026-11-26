import Girth.ContactTrainData
import Mathlib.Combinatorics.HalesJewett

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

def lineEdgeEmb (l : Combinatorics.Line E N) : E ↪ (N → E) where
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
      rw [hU i,hU k,hi,hk]
      rfl
    have hb' : P.endpoint (w i) b = P.endpoint (w k) b := by
      rw [hV i,hV k,hi,hk]
      rfl
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

end ContactPartiteEndpoints
end StructuralRamsey.Girth
