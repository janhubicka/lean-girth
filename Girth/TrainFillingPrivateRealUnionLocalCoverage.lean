import Girth.TrainFillingPrivateFirstWagonStrong

set_option Elab.async false

/-!
# Actual original first-wagon coverage, without a new assumption

An original first wagon F_p is a class of physical A-edges,
and its carrier is by definition the union of those edges.
For every old vertex x in its carrier we therefore have
a genuine ambient A-support edge e OWNED by wagon p with
x in e.

Since e lies entirely in V(F_p), its genuine relational
A-embedding factors through the induced local structure
D.induce V(F_p). This supplies the pointwise local
A-coverage hLocalCovered used by the unequal-summand
EHN private extension.

The only input is the authentic original wagon-vertex
coverage and the actual owner/edge containment equation.
No EHN X-coverage or output property is being assumed.

Candidate Lean source; exact-head compiler verification pending.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA V P : Type v}

/-- Every original F_p vertex lies in an ACTUAL induced
A-copy of that first wagon, whenever its carrier really
is the union of all ambient A-support edges owned by p.
No output EHN or shortened M witness is involved. -/
theorem originalFirstWagonLocalCoverage
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonCover : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ e : {e : Set V // e ∈ supportCopies A D},
        owner e = p ∧ x.1 ∈ e.1) :
    ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ a : Embedding A (D.induce (oldCarrier p)),
        x ∈ copyCarrier a := by
  intro p x
  obtain ⟨e, hOwner, hx⟩ := hWagonCover p x
  obtain ⟨a, ha⟩ := e.2
  have hInside : copyCarrier a ⊆ oldCarrier p := by
    rw [← ha]
    have hFull := hOwnerCarrier e
    rw [hOwner] at hFull
    exact hFull
  let inc := RelStructure.inclusion D (oldCarrier p)
  have hFactor : ∀ u : UA,
      ∃ y : {x : V // x ∈ oldCarrier p}, a u = inc y := by
    intro u
    refine ⟨⟨a u, hInside ⟨u, rfl⟩⟩, rfl⟩
  let b : Embedding A (D.induce (oldCarrier p)) :=
    a.factorThroughRange inc hFactor
  have hxA : x.1 ∈ copyCarrier a := by
    rw [← ha]
    exact hx
  obtain ⟨u, hu⟩ := hxA
  refine ⟨b, ⟨u, ?_⟩⟩
  have hSpec : a u = inc (b u) :=
    Classical.choose_spec (hFactor u)
  apply Subtype.ext
  exact hSpec.symm.trans hu

/-- The true disjoint-union W is A-covered as soon as the
original first-wagon carrier is its ACTUAL edge union,
with no additional coverage hypothesis on local induced
structures. -/
theorem realFirstWagonDisjointUnion_covered_of_owner
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hPositive : ∀ sym : L.Symbol, 0 < L.arity sym)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonCover : ∀ p (x : {x : V // x ∈ oldCarrier p}),
      ∃ e : {e : Set V // e ∈ supportCopies A D},
        owner e = p ∧ x.1 ∈ e.1) :
    ∀ w : FirstWagonUnionVertex oldCarrier,
      ∃ a : Embedding A
        (firstWagonDisjointUnion oldCarrier
          (fun p => D.induce (oldCarrier p))),
        w ∈ copyCarrier a := by
  exact firstWagonDisjointUnion_covered A oldCarrier
    (fun p => D.induce (oldCarrier p)) hPositive
    (originalFirstWagonLocalCoverage
      A D oldCarrier owner hOwnerCarrier hWagonCover)

end StructuralRamsey.Girth
