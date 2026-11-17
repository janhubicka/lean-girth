import Girth.Support
import Girth.TrainFillingPrivateColourBlockOrder

set_option Elab.async false

/-!
# The genuine disjoint union of unequal first wagons

At cutoff two, the first Ramsey target W is NOT any one first wagon.
It is the disjoint union of the individual relational first-wagon
structures F_p, which may be nonisomorphic and have unequal sizes.

This file constructs W itself, its literal component embeddings
and a coveredness theorem. A selected copy of W in X therefore
contains all F_p via the SAME selected W-embedding.

General RelLanguage supports nullary relations. For a nullary
symbol, the disjoint union's existential relation can hold in
one component but not in another, so component inclusions would
not be induced embeddings. The actual coloured-edge relational
language has only symbols of arity >=1 (edge arity k>=2, unary
colours, binary orders). We explicitly require positive arities.

One spanning A-relation (the genuine coloured ONE EDGE)
forces every A-copy in W to lie in one component. Therefore
each component inclusion is A-strong without a separately
assumed strongness field. All source coverage comes from
coverage in the original first wagons.

This is a source-only Lean candidate pending kernel compilation.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V P : Type v}

/-- Actual vertices of the tagged disjoint union of possibly
unequal local first-wagon relational types. -/
abbrev FirstWagonUnionVertex
    (oldCarrier : P → Set V) :=
  Sigma fun p : P => {x : V // x ∈ oldCarrier p}

/-- Relational disjoint union: each relation tuple must lie
entirely in a SINGLE summand, and carry that summand's
original relation. No new cross-summand edge is invented. -/
def firstWagonDisjointUnion
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p}) :
    RelStructure L (FirstWagonUnionVertex oldCarrier) where
  rel sym a :=
    ∃ (p : P) (t : Fin (L.arity sym) → {x : V // x ∈ oldCarrier p}),
      (∀ i, a i = ⟨p, t i⟩) ∧ (localStructure p).rel sym t

/-- Every source first wagon includes as an ACTUAL induced
relational substructure, provided the language has no nullary
relations. This arity condition is automatic for the concrete
coloured edge type of size at least two. -/
def firstWagonSummandEmbedding
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (p : P) :
    Embedding (localStructure p) (firstWagonDisjointUnion oldCarrier localStructure) where
  toFun x := ⟨p, x⟩
  injective := by
    intro x y h
    cases h
    rfl
  map_rel_iff := by
    intro sym x
    constructor
    · rintro ⟨q, t, hTuple, hRel⟩
      let i₀ : Fin (L.arity sym) := ⟨0, hPositive sym⟩
      have hpq : p = q :=
        congrArg Sigma.fst (hTuple i₀)
      subst q
      have ht : t = x := by
        funext i
        apply Subtype.ext
        exact (congrArg
          (fun w : FirstWagonUnionVertex oldCarrier => w.2.1)
          (hTuple i)).symm
      rw [ht] at hRel
      exact hRel
    · intro hRel
      exact ⟨p, x, fun _ => rfl, hRel⟩

/-- Every vertex in W lies in some genuine first-wagon
summand, without assuming a common first-wagon cardinality. -/
theorem firstWagonUnion_cover_by_summands
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (w : FirstWagonUnionVertex oldCarrier) :
    ∃ (p : P) (x : {x : V // x ∈ oldCarrier p}),
      firstWagonSummandEmbedding oldCarrier localStructure hPositive p x = w := by
  rcases w with ⟨p, x⟩
  exact ⟨p, x, rfl⟩

/-- Each A-copy has one spanning relation tuple.
For the actual coloured one-edge source A, choose its
full edge relation and its complete edge enumeration. -/
def HasSpanningRelation
    {UA : Type v} (A : RelStructure L UA) : Prop :=
  ∃ (sym : L.Symbol) (tuple : Fin (L.arity sym) → UA),
    A.rel sym tuple ∧ Function.Surjective tuple

/-- One relation tuple covering all A-vertices makes A
irreducible: every two distinct vertices occur together in
that same genuine relational tuple. This discharges the
standard irreducibility premise of functional EHN for the
actual coloured ONE-EDGE structure, rather than taking
irreducibility as an unexplained extra input. -/
theorem irreducible_of_spanningRelation
    {UA : Type v} (A : RelStructure L UA)
    (hSpan : HasSpanningRelation A) :
    A.Irreducible := by
  intro x y _hxy
  obtain ⟨sym, tuple, hRel, hSurj⟩ := hSpan
  obtain ⟨i, hi⟩ := hSurj x
  obtain ⟨j, hj⟩ := hSurj y
  exact ⟨sym, tuple, i, j, hRel, hi, hj⟩

/-- In a disjoint union, the image of a spanning A-relation
cannot cross different summands. Thus each A-copy is contained
in exactly one first-wagon component if it is nonempty.
We only need existence for the A-strongness argument. -/
theorem firstWagonUnion_Acopy_in_one_summand
    {UA : Type v} (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (a : Embedding A (firstWagonDisjointUnion oldCarrier localStructure)) :
    ∃ p : P,
      copyCarrier a ⊆
        Set.range (firstWagonSummandEmbedding oldCarrier localStructure hPositive p) := by
  obtain ⟨sym, tuple, hRel, hSurj⟩ := hSpan
  have hImage :
      (firstWagonDisjointUnion oldCarrier localStructure).rel sym
        (fun i => a (tuple i)) :=
    (a.map_rel_iff sym tuple).mpr hRel
  obtain ⟨p, t, hTuple, _ht⟩ := hImage
  refine ⟨p, ?_⟩
  rintro z ⟨u, hu⟩
  obtain ⟨i, hi⟩ := hSurj u
  refine ⟨t i, ?_⟩
  change (⟨p, t i⟩ : FirstWagonUnionVertex oldCarrier) = z
  calc
    (⟨p, t i⟩ : FirstWagonUnionVertex oldCarrier) =
        a (tuple i) := (hTuple i).symm
    _ = a u := congrArg a hi
    _ = z := hu

/-- Summand inclusion is A-strong: even a one-vertex
intersection with another component already identifies the
only component containing the spanning A-copy. No false
assumption that A-linear old EDGES force F_p carrier linearity. -/
theorem firstWagonSummandEmbedding_aStrong
    {UA : Type v} (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hSpan : HasSpanningRelation A)
    (p : P) :
    AStrong A (firstWagonDisjointUnion oldCarrier localStructure)
      (copyCarrier (firstWagonSummandEmbedding oldCarrier localStructure hPositive p)) := by
  intro a hMeet
  obtain ⟨q, hCopy⟩ :=
    firstWagonUnion_Acopy_in_one_summand A oldCarrier localStructure
      hPositive hSpan a
  by_cases hpq : q = p
  · subst q
    exact hCopy
  · have hSmall :
        (copyCarrier a ∩
          copyCarrier
            (firstWagonSummandEmbedding oldCarrier localStructure hPositive p)).Subsingleton := by
      intro z hz w hw
      obtain ⟨x, hx⟩ := hCopy hz.1
      obtain ⟨y, hy⟩ := hz.2
      have hqp : q = p :=
        congrArg Sigma.fst (hx.trans hy.symm)
      exact False.elim (hpq hqp)
    exact False.elim (hMeet hSmall)

/-- If every F_p is covered by its original A-edges,
then its genuinely constructed disjoint union W is
A-covered. This is required before trimming unused
EHN X vertices and proving the first Ramsey arrow. -/
theorem firstWagonDisjointUnion_covered
    {UA : Type v} (A : RelStructure L UA)
    (oldCarrier : P → Set V)
    (localStructure : (p : P) → RelStructure L {x : V // x ∈ oldCarrier p})
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hLocalCover : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : Embedding A (localStructure p), x ∈ copyCarrier a) :
    ∀ w : FirstWagonUnionVertex oldCarrier,
      ∃ a : Embedding A (firstWagonDisjointUnion oldCarrier localStructure),
        w ∈ copyCarrier a := by
  rintro ⟨p, x⟩
  obtain ⟨a, hx⟩ := hLocalCover p x
  obtain ⟨u, hu⟩ := hx
  refine ⟨(firstWagonSummandEmbedding oldCarrier localStructure hPositive p).comp a,
    ⟨u, ?_⟩⟩
  change (⟨p, a u⟩ : FirstWagonUnionVertex oldCarrier) = ⟨p, x⟩
  exact congrArg (fun y : {x : V // x ∈ oldCarrier p} =>
    (⟨p, y⟩ : FirstWagonUnionVertex oldCarrier)) hu

end StructuralRamsey.Girth
