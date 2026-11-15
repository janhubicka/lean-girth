import Girth.TrainFillingPrivateFirstWagonStrong
import Girth.TrainFillingPrivateRealUnionLinear

set_option Elab.async false

/-!
# The ORIGINAL physical edge type equals the disjoint local wagon edges

The genuine original T-edge type is the subtype of ALL
A-support carriers of its relational structure D.
The private-extension construction instead indexes
each selected original edge as an owner p together with
a local A-support edge of the induced first wagon F_p.

These types are equivalent when the source carries
its ACTUAL edge-owner function, every edge is contained
in its owner's first-wagon carrier, and different
first-wagon carriers meet in at most one vertex.

Surjectivity: each original A-embedding factors into
the induced structure on its owner's complete carrier.
Injectivity: the induced F_p edge has the correct unique
original owner (already proved by first-wagon linearity),
and Subtype.val is injective on local vertices.

This is the precise source-edge identification required
to transport the original T train and its selected target
to the previously constructed tagged private-choice edges.
No new Ramsey, output strongness or girth premise.

Uncompiled Lean candidate, no sorries or new axioms.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA V P : Type v}

/-- Disjoint family of the genuine induced source
A-support edges of each first wagon. Distinct p
labels are retained even if old carriers coincide. -/
abbrev OriginalFirstWagonEdges
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V) :=
  Sigma fun p : P =>
    {f : Set {x : V // x ∈ oldCarrier p} //
      f ∈ supportCopies A (D.induce (oldCarrier p))}

/-- The literal ambient physical A-edge obtained from one
owner-tagged induced F_p A-support edge by forgetting the
local vertex subtype, with its support-copy witness. -/
noncomputable def firstWagonEdgeToOriginal
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V) :
    OriginalFirstWagonEdges A D oldCarrier →
      {e : Set V // e ∈ supportCopies A D}
    | ⟨p, f⟩ =>
        ⟨Subtype.val '' f.1, by
          obtain ⟨a, ha⟩ := f.2
          refine ⟨(RelStructure.inclusion D (oldCarrier p)).comp a, ?_⟩
          rw [ha]
          exact UniformPrivateTemplate.image_copyCarrier_comp
            A (D.induce (oldCarrier p)) D
              (RelStructure.inclusion D (oldCarrier p)) a⟩

/-- Every induced first-wagon support edge has exactly
the owner supplied by its p label. The crucial
no-foreign-induced-edge result follows from
first-wagon carrier linearity, not just old edge
linearity. -/
theorem firstWagonEdgeToOriginal_owner
    [Nontrivial UA]
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonLinear : ∀ p q : P, p ≠ q →
      (oldCarrier p ∩ oldCarrier q).Subsingleton)
    (e : OriginalFirstWagonEdges A D oldCarrier) :
    owner (firstWagonEdgeToOriginal A D oldCarrier e) = e.1 := by
  rcases e with ⟨p, f⟩
  obtain ⟨a, ha⟩ := f.2
  let inc := RelStructure.inclusion D (oldCarrier p)
  have hEq :
      firstWagonEdgeToOriginal A D oldCarrier ⟨p, f⟩ =
        (⟨copyCarrier (inc.comp a), ⟨inc.comp a, rfl⟩⟩ :
          {e : Set V // e ∈ supportCopies A D}) := by
    apply Subtype.ext
    change Subtype.val '' f.1 = copyCarrier (inc.comp a)
    rw [ha]
    exact UniformPrivateTemplate.image_copyCarrier_comp
      A (D.induce (oldCarrier p)) D inc a
  rw [hEq]
  exact originalFirstWagonInducedACopy_owner
    A D oldCarrier owner hOwnerCarrier hWagonLinear p a

/-- Every original full A-support edge has a local A-copy
in its OWN first wagon, because its complete carrier
is contained there. This is the true surjectivity
of forgetting the owner-labelled induced structure. -/
theorem firstWagonEdgeToOriginal_surjective
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e)) :
    Function.Surjective
      (firstWagonEdgeToOriginal A D oldCarrier) := by
  intro e
  obtain ⟨a, ha⟩ := e.2
  let p := owner e
  let inc := RelStructure.inclusion D (oldCarrier p)
  have hInside : copyCarrier a ⊆ oldCarrier p := by
    rw [← ha]
    exact hOwnerCarrier e
  have hFactor : ∀ x : UA,
      ∃ y : {x : V // x ∈ oldCarrier p}, a x = inc y := by
    intro x
    exact ⟨⟨a x, hInside ⟨x, rfl⟩⟩, rfl⟩
  let b : Embedding A (D.induce (oldCarrier p)) :=
    a.factorThroughRange inc hFactor
  have hComp : inc.comp b = a := by
    apply Embedding.ext
    intro x
    exact (Classical.choose_spec (hFactor x)).symm
  let f : {f : Set {x : V // x ∈ oldCarrier p} //
      f ∈ supportCopies A (D.induce (oldCarrier p))} :=
    ⟨copyCarrier b, ⟨b, rfl⟩⟩
  refine ⟨⟨p, f⟩, ?_⟩
  apply Subtype.ext
  change Subtype.val '' copyCarrier b = e.1
  calc
    Subtype.val '' copyCarrier b = copyCarrier (inc.comp b) :=
      UniformPrivateTemplate.image_copyCarrier_comp
        A (D.induce (oldCarrier p)) D inc b
    _ = copyCarrier a := congrArg copyCarrier hComp
    _ = e.1 := ha.symm

/-- No two differently owned or differently embedded
local A-support edges become the same original A-support
carrier. The first-wagon carrier linearity identifies
their owner labels; then injectivity of Subtype.val
identifies the local carrier sets. -/
theorem firstWagonEdgeToOriginal_injective
    [Nontrivial UA]
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonLinear : ∀ p q : P, p ≠ q →
      (oldCarrier p ∩ oldCarrier q).Subsingleton) :
    Function.Injective
      (firstWagonEdgeToOriginal A D oldCarrier) := by
  rintro ⟨p, f⟩ ⟨q, g⟩ hEq
  have hpq : p = q := by
    calc
      p = owner (firstWagonEdgeToOriginal A D oldCarrier ⟨p, f⟩) :=
        (firstWagonEdgeToOriginal_owner A D oldCarrier
          owner hOwnerCarrier hWagonLinear ⟨p, f⟩).symm
      _ = owner (firstWagonEdgeToOriginal A D oldCarrier ⟨q, g⟩) :=
        congrArg owner hEq
      _ = q :=
        firstWagonEdgeToOriginal_owner A D oldCarrier
          owner hOwnerCarrier hWagonLinear ⟨q, g⟩
  subst q
  have hImage : Subtype.val '' f.1 = Subtype.val '' g.1 :=
    congrArg (fun z : {e : Set V // e ∈ supportCopies A D} => z.1) hEq
  have hLocal : f.1 = g.1 := by
    ext x
    constructor
    · intro hx
      have hh : x.1 ∈ Subtype.val '' g.1 := by
        rw [← hImage]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hh
      exact (Subtype.ext hyx) ▸ hy
    · intro hx
      have hh : x.1 ∈ Subtype.val '' f.1 := by
        rw [hImage]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hh
      exact (Subtype.ext hyx) ▸ hy
  have hFG : f = g := Subtype.ext hLocal
  cases hFG
  rfl

/-- The genuine original physical edge type is EXACTLY
the dependent union of the original induced first-wagon
support edges, using the true owner map and carrier
linearity of T. This is the missing edge-type
equivalence for the original T-to-filled-target arrow. -/
noncomputable def originalFirstWagonEdgeEquiv
    [Nontrivial UA]
    (A : RelStructure L UA)
    (D : RelStructure L V)
    (oldCarrier : P → Set V)
    (owner : {e : Set V // e ∈ supportCopies A D} → P)
    (hOwnerCarrier : ∀ e, e.1 ⊆ oldCarrier (owner e))
    (hWagonLinear : ∀ p q : P, p ≠ q →
      (oldCarrier p ∩ oldCarrier q).Subsingleton) :
    OriginalFirstWagonEdges A D oldCarrier ≃
      {e : Set V // e ∈ supportCopies A D} :=
  Equiv.ofBijective (firstWagonEdgeToOriginal A D oldCarrier)
    ⟨firstWagonEdgeToOriginal_injective
      A D oldCarrier owner hOwnerCarrier hWagonLinear,
     firstWagonEdgeToOriginal_surjective
      A D oldCarrier owner hOwnerCarrier⟩

end StructuralRamsey.Girth
