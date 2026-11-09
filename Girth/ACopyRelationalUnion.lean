import Girth.ACopyInducedLinkSupport

set_option autoImplicit false

/-!
# Relational union on an exact point quotient

This is the relational half of the decorated A-copy star. Given injective
core/source point maps and agreement of the *full induced* relations on
overlapping tuples, define the union of all source relation tuples on the
already-constructed point quotient. The source point maps are then
induced relational embeddings, not just homomorphisms.

No hypergraph linearity, Ramsey input, or completeness of A-copy support is
assumed or inferred here; those are separate from relational reflection.
-/

namespace StructuralRamsey.Girth.ACopyRelationalUnion

open StructuralRamsey.RelStructure

universe u v

variable {L : RelLanguage.{u}}
variable {CorePoint Point I : Type v} {SourcePoint : I → Type v}
variable (C : RelStructure L CorePoint)
variable (S : (i : I) → RelStructure L (SourcePoint i))
variable (core : CorePoint → Point) (source : (i : I) → SourcePoint i → Point)

/-- A relation holds in the free relational union precisely when it is
contributed by a core or source chart. Every point still exists, even when
it is unsupported by any physical A-edge. -/
def UnionRel (sym : L.Symbol) (t : Fin (L.arity sym) → Point) : Prop :=
  (∃ x : Fin (L.arity sym) → CorePoint,
    (∀ k, core (x k) = t k) ∧ C.rel sym x) ∨
  (∃ i : I, ∃ x : Fin (L.arity sym) → SourcePoint i,
    (∀ k, source i (x k) = t k) ∧ (S i).rel sym x)

def union : RelStructure L Point where
  rel := UnionRel C S core source

/-- Core and source relations agree whenever their tuples have precisely
the same image in the quotient. This is the relational content of an
induced gluing link, stronger than agreement of point equality alone. -/
def CoreSourceAgreement : Prop :=
  ∀ i (sym : L.Symbol)
    (x : Fin (L.arity sym) → CorePoint)
    (y : Fin (L.arity sym) → SourcePoint i),
      (∀ k, core (x k) = source i (y k)) →
        (C.rel sym x ↔ (S i).rel sym y)

def SourceSourceAgreement : Prop :=
  ∀ i j (sym : L.Symbol)
    (x : Fin (L.arity sym) → SourcePoint i)
    (y : Fin (L.arity sym) → SourcePoint j),
      (∀ k, source i (x k) = source j (y k)) →
        ((S i).rel sym x ↔ (S j).rel sym y)

/-- No new tuples appear in the induced core chart, even when they were
contributed by a different source chart. -/
def coreEmbedding
    (hCore : Function.Injective core)
    (hAgree : CoreSourceAgreement C S core source) :
    Embedding C (union C S core source) where
  toFun := core
  injective := hCore
  map_rel_iff := by
    intro sym x
    constructor
    · intro hx
      exact Or.inl ⟨x, (fun _ => rfl), hx⟩
    · intro hx
      rcases hx with ⟨y, hy, hr⟩ | ⟨i, y, hy, hr⟩
      · have hxy : y = x := by
          funext k
          exact hCore (hy k)
        simpa [hxy] using hr
      · exact (hAgree i sym x y (fun k => (hy k).symm)).mpr hr

/-- The same for any source. Relations contributed by other standards
are reflected using full overlap agreement, not just point equality. -/
def sourceEmbedding (i : I)
    (hSource : Function.Injective (source i))
    (hAgree : CoreSourceAgreement C S core source)
    (hSourceAgree : SourceSourceAgreement C S core source) :
    Embedding (S i) (union C S core source) where
  toFun := source i
  injective := hSource
  map_rel_iff := by
    intro sym x
    constructor
    · intro hx
      exact Or.inr ⟨i, x, (fun _ => rfl), hx⟩
    · intro hx
      rcases hx with ⟨y, hy, hr⟩ | ⟨j, y, hy, hr⟩
      · exact (hAgree i sym y x (fun k => hy k)).mp hr
      · exact (hSourceAgree j i sym y x (fun k => hy k)).mp hr

/-- In an exact star, two different standards intersect only inside
the core. Agreement of the core with each standard consequently gives
agreement between *all* standards, also for nullary relations.
The same-source case uses injectivity instead of a core witness. -/
theorem sourceAgreement_of_core
    (hSrc : ∀ i, Function.Injective (source i))
    (hCross : ∀ i j, i ≠ j →
      ∀ p, p ∈ Set.range (source i) ∩ Set.range (source j) →
        p ∈ Set.range core)
    (hAgree : CoreSourceAgreement C S core source) :
    SourceSourceAgreement C S core source := by
  intro i j sym x y hxy
  by_cases hij : i = j
  · subst j
    have h : x = y := by
      funext k
      exact hSrc i (hxy k)
    subst y
    exact Iff.rfl
  · have hPre : ∀ k, ∃ z : CorePoint, core z = source i (x k) := by
      intro k
      have hx : source i (x k) ∈ Set.range (source i) :=
        ⟨x k, rfl⟩
      have hy : source i (x k) ∈ Set.range (source j) :=
        ⟨y k, (hxy k).symm⟩
      obtain ⟨z, hz⟩ := hCross i j hij _ ⟨hx, hy⟩
      exact ⟨z, hz.symm⟩
    let z : Fin (L.arity sym) → CorePoint := fun k => Classical.choose (hPre k)
    have hzx : ∀ k, core (z k) = source i (x k) :=
      fun k => Classical.choose_spec (hPre k)
    have hzy : ∀ k, core (z k) = source j (y k) :=
      fun k => (hzx k).trans (hxy k)
    exact (hAgree i sym z x hzx).symm.trans (hAgree j sym z y hzy)

end StructuralRamsey.Girth.ACopyRelationalUnion
