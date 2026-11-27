import Girth.ContactWordStrip
import PartiteConstruction.Ramsey.Finite
import Mathlib.Order.Prod.Lex.Basic

/-! The elementary non-induced ordered Ramsey seed, using the
proved finite Ramsey theorem for increasing tuples. The edges
of the seed are literal increasing tuples of positions, labelled
by the common part word of the original uniform edges. -/

namespace StructuralRamsey.Girth
universe v
variable {V E I P : Type v}

/-- Each edge has a fixed size and the same word of part labels
when read in the concatenated part order. -/
structure ContactOrderedEdgeWord (D : ContactHypergraphData V E I)
    [LinearOrder V] (P : Type v) (a : ℕ) where
  part : V → P
  word : Fin a → P
  enumeration : E → Fin a ↪o V
  carrier_eq : ∀ e, D.edgeCarrier e = Set.range (enumeration e)
  part_eq : ∀ e i, part (enumeration e i) = word i

universe w

/-- Finiteness of order embeddings via their underlying maps. -/
theorem contactFiniteOrderEmbedding (U : Type v) (W : Type w) [Preorder U] [Preorder W]
    [Finite U] [Finite W] : Finite (U ↪o W) :=
  Finite.of_injective (fun f : U ↪o W => (f : U → W)) (by
    intro f g he
    ext x
    exact congrFun he x)

namespace ContactOrderedEdgeWord
variable {D : ContactHypergraphData V E I} [LinearOrder V]
    {a : ℕ} (A : ContactOrderedEdgeWord D P a)

/-- The raw seed is not assumed linear or induced. It records
only the actual edge and vertex embeddings of the target. -/
abbrev SeedVertex (_A : ContactOrderedEdgeWord D P a) (N : ℕ) := Fin N × P

-- The contact data use one universe for vertices, edge labels, and copies.
abbrev SeedEdge (_A : ContactOrderedEdgeWord D P a) (N : ℕ) : Type v :=
  ULift.{v} (Fin a ↪o Fin N)

theorem seedEdgeFinite (N : ℕ) : Finite (A.SeedEdge N) :=
  Finite.of_injective (fun e : A.SeedEdge N => (e.down : Fin a → Fin N)) (by
    rintro ⟨e⟩ ⟨f⟩ he
    have h : e = f := by
      ext i
      exact congrArg Fin.val (congrFun he i)
    exact congrArg ULift.up h)

def seedCarrier (N : ℕ) (e : A.SeedEdge N) : Set (A.SeedVertex N) :=
  Set.range (fun i => (e.down i,A.word i))

def seedHypergraph (N : ℕ) :
    ContactHypergraphData (A.SeedVertex N) (A.SeedEdge N) PEmpty.{v+1} where
  edgeCarrier := A.seedCarrier N
  copyCarrier := PEmpty.elim
  copyEdges := PEmpty.elim

def seedVertexMap {N : ℕ} (j : V ↪o Fin N) : V ↪ A.SeedVertex N where
  toFun x := (j x,A.part x)
  inj' := by
    intro x y he
    exact j.injective (congrArg Prod.fst he)

def seedEdgeMap {N : ℕ} (j : V ↪o Fin N)
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e)) : E ↪ A.SeedEdge N where
  toFun e := ⟨(A.enumeration e).trans j⟩
  inj' := by
    intro e f h
    apply hinj
    change D.edgeCarrier e = D.edgeCarrier f
    rw [A.carrier_eq,A.carrier_eq]
    have he : (A.enumeration e : Fin a → V) = A.enumeration f := by
      funext i
      exact j.injective (congrArg (fun k : A.SeedEdge N => k.down i) h)
    rw [he]

theorem seed_carrier_image {N : ℕ} (j : V ↪o Fin N)
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e)) (e : E) :
    (A.seedHypergraph N).edgeCarrier (A.seedEdgeMap j hinj e) =
      A.seedVertexMap j '' D.edgeCarrier e := by
  rw [A.carrier_eq]
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨A.enumeration e i,⟨i,rfl⟩,?_⟩
    exact Prod.ext rfl (A.part_eq e i)
  · rintro ⟨u,⟨i,rfl⟩,rfl⟩
    exact ⟨i,Prod.ext rfl (A.part_eq e i).symm⟩

/-- The raw seed arrow is a direct finite Ramsey application.
A colour of an increasing tuple is the colour of its actual
seed edge. Non-increasing tuples receive an arbitrary colour. -/
theorem exists_raw_seed_arrow [Fintype V] {Color : Type v} [Fintype Color]
    [Nonempty Color] [Nonempty E]
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e)) :
    ∃ N : ℕ, ∀ χ : A.SeedEdge N → Color,
      ∃ j : V ↪o Fin N, ∃ c : Color, ∀ e : E,
        χ (A.seedEdgeMap j hinj e) = c := by
  classical
  obtain ⟨N,hN⟩ := StructuralRamsey.FiniteRamsey.strictMono Color a (Fintype.card V)
  refine ⟨N,?_⟩
  intro χ
  let ρ : (Fin a → Fin N) → Color := fun f =>
    if hf : StrictMono f then χ ⟨OrderEmbedding.ofStrictMono f hf⟩
    else Classical.choice (inferInstance : Nonempty Color)
  obtain ⟨s,hs,hm⟩ := hN ρ
  let j : V ↪o Fin N :=
    ((Fintype.orderIsoFinOfCardEq V rfl).symm.toOrderEmbedding).trans
      (s.orderEmbOfCardLe hs)
  let e₀ : E := Classical.choice inferInstance
  refine ⟨j,χ (A.seedEdgeMap j hinj e₀),?_⟩
  intro e
  let f := (A.seedEdgeMap j hinj e).down
  let g := (A.seedEdgeMap j hinj e₀).down
  have hf : StrictMono f := f.strictMono
  have hg : StrictMono g := g.strictMono
  have hmem (u : E) (i : Fin a) :
      (A.seedEdgeMap j hinj u).down i ∈ s :=
    s.orderEmbOfCardLe_mem hs ((Fintype.orderIsoFinOfCardEq V rfl).symm (A.enumeration u i))
  have he := hm f g hf hg (hmem e) (hmem e₀)
  have heq (k : Fin a ↪o Fin N) :
      OrderEmbedding.ofStrictMono k k.strictMono = k := by
    ext i
    rfl
  have he' : χ (⟨f⟩ : A.SeedEdge N) = χ ⟨g⟩ := by
    simpa only [ρ,dif_pos hf,dif_pos hg,heq] using he
  exact he'

/-- In picture zero each target image is a separate component,
so its edge map is strong there even though the raw seed is
not induced. The designated labels are retained separately. -/
def rawInitialProjection (N : ℕ)
    (hinj : Function.Injective (fun e : E => D.edgeCarrier e)) :
    ContactBaseProjection (D.disjointCopies (V ↪o Fin N)).noCopies (A.seedCarrier N) where
  vertex := fun x => A.seedVertexMap x.1 x.2
  edge := fun e => A.seedEdgeMap e.1 hinj e.2
  edge_image := by
    rintro ⟨j,e⟩
    change _ = (A.seedHypergraph N).edgeCarrier (A.seedEdgeMap j hinj e)
    rw [A.seed_carrier_image j hinj]
    ext x
    constructor
    · rintro ⟨⟨k,y⟩,⟨hk,hy⟩,he⟩
      change k = j at hk
      subst k
      exact ⟨y,hy,he⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(j,y),⟨rfl,hy⟩,rfl⟩
  edge_inj := by
    rintro ⟨j,e⟩ ⟨k,x⟩ hx ⟨l,y⟩ hy he
    obtain ⟨hk,_⟩ := hx
    obtain ⟨hl,_⟩ := hy
    change k = j at hk
    change l = j at hl
    subst k
    subst l
    exact Prod.ext rfl ((A.seedVertexMap j).injective he)
  copy_inj := by intro i; cases i
  copy_edge_subset := by intro i; cases i
  copy_strong := by intro i; cases i

theorem rawInitial_linear (N : ℕ)
    (hlin : ∀ e f : E, e ≠ f → (D.edgeCarrier e ∩ D.edgeCarrier f).Subsingleton) :
    ∀ e f : (V ↪o Fin N) × E, e ≠ f →
      (((D.disjointCopies (V ↪o Fin N)).noCopies).edgeCarrier e ∩
        ((D.disjointCopies (V ↪o Fin N)).noCopies).edgeCarrier f).Subsingleton := by
  rintro ⟨i,e⟩ ⟨j,f⟩ hne x hx y hy
  have hij : i = j := hx.1.1.symm.trans hx.2.1
  subst j
  exact Prod.ext (hx.1.1.trans hy.1.1.symm)
    (hlin e f (fun he => hne (congrArg (Prod.mk i) he))
      ⟨hx.1.2,hx.2.2⟩ ⟨hy.1.2,hy.2.2⟩)

end ContactOrderedEdgeWord
end StructuralRamsey.Girth
