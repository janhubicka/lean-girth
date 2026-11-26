import Girth.ContactWordBase
import Girth.ContactCutoffTwoInput

/-! The actual word template for cutoff two. First make the
first wagons vertex-disjoint, retaining every original edge
label. Apply the word construction to this linear a-partite
hypergraph. Restrict each line to each first wagon; this is
the concrete TemplateEmbedding required by the shorter input. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I A : Type v}

namespace ContactPartiteEndpoints
variable {m : ℕ} {D : ContactHypergraphData V E I}
    (P : ContactPartiteEndpoints D A)
    (T : ContactTrainData E (m+1))

abbrev firstCarrier (p : T.FirstWagon) :=
  (D.atCut (T.parent (0 : Fin (m+1)).succ)).contactWagonCarrier p

/-- A vertex is an actual vertex of a first wagon, with that
wagon's tag. The same original vertex may occur at several tags. -/
abbrev FirstVertex := Sigma (fun p : T.FirstWagon => firstCarrier (D := D) T p)

def firstTag (p : T.FirstWagon) : firstCarrier (D := D) T p ↪ FirstVertex (D := D) T :=
  ⟨Sigma.mk p,by intro u v h; cases h; rfl⟩

def firstEndpoint (e : E) (a : A) : FirstVertex (D := D) T :=
  ⟨T.parent (0 : Fin (m+1)).succ e,
    ⟨P.endpoint e a,e,rfl,P.endpoint_mem e a⟩⟩

def firstDisjoint : ContactHypergraphData (FirstVertex (D := D) T) E PEmpty.{v+1} where
  edgeCarrier := fun e => Set.range (P.firstEndpoint T e)
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

def firstPart (x : FirstVertex (D := D) T) : A := P.part x.2.val

/-- The disjoint union remains genuinely a-partite and covered. -/
def firstEndpoints : ContactPartiteEndpoints (P.firstDisjoint T) A where
  part := P.firstPart T
  endpoint := P.firstEndpoint T
  part_endpoint := P.part_endpoint
  carrier_eq := fun _ => rfl
  covered := by
    rintro ⟨p,⟨x,e,he,hx⟩⟩
    subst p
    refine ⟨e,P.part x,?_⟩
    have h := P.endpoint_of_mem e x hx
    change (⟨T.parent (0 : Fin (m+1)).succ e,
      ⟨P.endpoint e (P.part x),e,rfl,P.endpoint_mem e (P.part x)⟩⟩ :
        FirstVertex (D := D) T) = _
    cases h
    rfl

/-- Linearity is inherited inside each original wagon; two
different wagon tags have disjoint vertex carriers. -/
theorem firstDisjoint_linear
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ∀ e f : E, e ≠ f →
      ((P.firstDisjoint T).edgeCarrier e ∩ (P.firstDisjoint T).edgeCarrier f).Subsingleton := by
  intro e f hne x hx y hy
  obtain ⟨a,ha⟩ := hx.1
  obtain ⟨b,hb⟩ := hx.2
  obtain ⟨c,hc⟩ := hy.1
  obtain ⟨d,hd⟩ := hy.2
  have hx' : P.endpoint e a = P.endpoint f b :=
    congrArg (fun z : FirstVertex (D := D) T => z.2.val) (ha.trans hb.symm)
  have hy' : P.endpoint e c = P.endpoint f d :=
    congrArg (fun z : FirstVertex (D := D) T => z.2.val) (hc.trans hd.symm)
  have he := hlin e f hne
    ⟨P.endpoint_mem e a,hx'.symm ▸ P.endpoint_mem f b⟩
    ⟨P.endpoint_mem e c,hy'.symm ▸ P.endpoint_mem f d⟩
  exact ha.symm.trans ((congrArg (P.firstEndpoint T e) (P.endpoint_inj e he)).trans hc)

/-- Actual incidence in a tagged first wagon. -/
theorem firstEndpoint_tag (e : E) (a : A) :
    (P.firstEndpoint T e).1 = T.parent (0 : Fin (m+1)).succ e := rfl

theorem firstDisjoint_allowed (allowed : Set A)
    (hpar : D.Parameter T 0 (0 : Fin (m+1)).succ (P.part ⁻¹' allowed))
    (e f : E) (hne : e ≠ f) (x : FirstVertex (D := D) T)
    (hx : x ∈ (P.firstDisjoint T).edgeCarrier e ∩ (P.firstDisjoint T).edgeCarrier f) :
    P.firstPart T x ∈ allowed := by
  obtain ⟨a,ha⟩ := hx.1
  obtain ⟨b,hb⟩ := hx.2
  have he : T.parent (0 : Fin (m+1)).succ e = T.parent (0 : Fin (m+1)).succ f :=
    congrArg Sigma.fst (ha.trans hb.symm)
  have hx₁ : x.2.val ∈ D.edgeCarrier e :=
    congrArg (fun z : FirstVertex (D := D) T => z.2.val) ha ▸ P.endpoint_mem e a
  have hx₂ : x.2.val ∈ D.edgeCarrier f :=
    congrArg (fun z : FirstVertex (D := D) T => z.2.val) hb ▸ P.endpoint_mem f b
  by_contra hn
  exact hne (T.bottom (hpar e f x.2.val he hx₁ hx₂ hn))

variable (N : Type)

/-- The actual word template based on the disjoint first wagons. -/
abbrev CutoffWordVertex := (P.firstEndpoints T).WordVertex N

def cutoffTemplate : ContactHypergraphData (P.CutoffWordVertex T N)
    (N → E) (Combinatorics.Line E N) :=
  (P.firstEndpoints T).wordHypergraph N

/-- Restrict a single actual line to each first wagon. -/
def linePadding (l : Combinatorics.Line E N) :
    ContactWagonPadding (firstCarrier (D := D) T) (P.CutoffWordVertex T N) where
  inside := fun p => (firstTag (D := D) T p).trans ((P.firstEndpoints T).lineVertexEmb N l)

noncomputable def lineTemplate
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton)
    (l : Combinatorics.Line E N) :
    (P.linePadding T N l).TemplateEmbedding (P.cutoffTemplate T N) where
  edge := (P.firstEndpoints T).lineEdgeEmb N l
  edge_image := by
    intro e
    rw [show (P.cutoffTemplate T N).edgeCarrier ((P.firstEndpoints T).lineEdgeEmb N l e) =
      (P.firstEndpoints T).wordCarrier N ((P.firstEndpoints T).lineEdgeEmb N l e) from rfl,
      (P.firstEndpoints T).line_carrier]
    ext x
    constructor
    · rintro ⟨z,⟨a,rfl⟩,rfl⟩
      exact ⟨P.endpoint e a,P.endpoint_mem e a,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      let a := P.part y
      have he := P.endpoint_of_mem e y hy
      refine ⟨P.firstEndpoint T e a,⟨a,rfl⟩,?_⟩
      change (P.firstEndpoints T).lineVertexEmb N l (P.firstEndpoint T e a) =
        (P.firstEndpoints T).lineVertexEmb N l
          (⟨T.parent (0 : Fin (m+1)).succ e,⟨y,e,rfl,hy⟩⟩ : FirstVertex (D := D) T)
      congr 1
      change (⟨T.parent (0 : Fin (m+1)).succ e,
        ⟨P.endpoint e a,e,rfl,P.endpoint_mem e a⟩⟩ : FirstVertex (D := D) T) = _
      cases he
      rfl
  edge_inj := by
    intro e f _ he
    exact ((P.firstEndpoints T).lineEdgeEmb N l).injective he
  strong := by
    intro p f hn
    let Q := P.firstEndpoints T
    let emb := Q.lineVertexEmb N l
    obtain ⟨x,hx,y,hy,hxy⟩ := hn
    obtain ⟨u,hu⟩ := hx.2
    obtain ⟨v,hv⟩ := hy.2
    have hU : x ∈ Set.range emb := ⟨firstTag (D := D) T p u,hu⟩
    have hV : y ∈ Set.range emb := ⟨firstTag (D := D) T p v,hv⟩
    obtain ⟨e,he⟩ := Q.line_strong N (P.firstDisjoint_linear T hlin) l f
      ⟨x,⟨hx.1,hU⟩,y,⟨hy.1,hV⟩,hxy⟩
    have hx' := hx.1
    change x ∈ Q.wordCarrier N f at hx'
    rw [← he,Q.line_carrier] at hx'
    obtain ⟨z,hz,hz'⟩ := hx'
    obtain ⟨a,ha⟩ := hz
    have htag : firstTag (D := D) T p u = P.firstEndpoint T e a :=
      emb.injective (hu.trans (hz'.symm.trans (congrArg emb ha.symm)))
    exact ⟨e,(congrArg Sigma.fst htag).symm,he⟩

/-- Every word-template intersection is in an allowed first
parameter part. This is stronger than mere linearity. -/
theorem cutoffTemplate_allowed (allowed : Set A)
    (hpar : D.Parameter T 0 (0 : Fin (m+1)).succ (P.part ⁻¹' allowed))
    (e f : N → E) (hne : e ≠ f) (x : P.CutoffWordVertex T N)
    (hx : x ∈ (P.cutoffTemplate T N).edgeCarrier e ∩ (P.cutoffTemplate T N).edgeCarrier f) :
    (P.firstEndpoints T).wordPart N x ∈ allowed := by
  let Q := P.firstEndpoints T
  obtain ⟨u,v,huv,he⟩ := Q.word_intersection_part N e f hne x hx
  have hmem : Q.endpoint u (Q.wordPart N x) ∈
      (P.firstDisjoint T).edgeCarrier u ∩ (P.firstDisjoint T).edgeCarrier v :=
    ⟨⟨_,rfl⟩,⟨_,he.symm⟩⟩
  have h := P.firstDisjoint_allowed T allowed hpar u v huv _ hmem
  change P.firstPart T (P.firstEndpoint T u (Q.wordPart N x)) ∈ allowed at h
  change P.part (P.endpoint u (Q.wordPart N x)) ∈ allowed at h
  rw [P.part_endpoint] at h
  exact h

/-- A concrete shorter input from the word template; all its
local TemplateEmbedding fields have been constructed. -/
noncomputable def cutoffInput (hm : 0 < m) [Nonempty E]
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ContactCutoffTwoInput D T (P.cutoffTemplate T N) (Combinatorics.Line E N) where
  tail_pos := hm
  cover := (P.firstEndpoints T).word_covered N
  nonempty := ⟨fun _ => Classical.choice inferInstance⟩
  pad := P.linePadding T N
  line := P.lineTemplate T N hlin

/-- The line colouring assertion for the exact input, obtained
from the same word Ramsey theorem. -/
theorem cutoffInput_arrow [Finite E] {Color : Type v} [Finite Color] :
    ∃ (N : Type) (_ : Fintype N), ∀ χ : (N → E) → Color,
      ∃ l : Combinatorics.Line E N, ∃ c : Color, ∀ e,
        χ ((P.firstEndpoints T).lineEdgeEmb N l e) = c :=
  (P.firstEndpoints T).exists_word_arrow

end ContactPartiteEndpoints
end StructuralRamsey.Girth
