import Girth.ForestMultiOwnerKernel
import Mathlib.Tactic

/-!
# Canonical carrier-faithful evaluation of one owner-gluing kernel

The correct finite event object for multiple standard-picture owners is
not a single injection of the old picture. It is a quotient of the
disjoint owner-tagged copies (q,x) by the prescribed port-identification
equivalence.

When the relation identifies no distinct vertices INSIDE any single
owner, every owner copy injects into the quotient. Any other system of
owner embeddings realizing the same cross-owner identifications has
exactly the same finite forest predicate as this canonical quotient
model.

This gives a canonical evaluation for ONE FIXED finite gluing record,
not the missing functorial evaluation of the whole infinite free
ancestral successor tree or the geometric existence of the required
port-gluing records.
-/

namespace StructuralRamsey.Girth

universe v

/-- An equivalence relation recording precisely which tagged old
vertices of different standard-picture owners must be identified.
Within any single owner it can identify only equal source vertices. -/
structure OwnerGluingKernel (Q Old : Type v) where
  relation : Setoid (Q × Old)
  sameOwner : ∀ q : Q, ∀ x y : Old,
    relation.r (q, x) (q, y) → x = y

/-- Each owner has a canonical injective image in the vertex quotient
of the gluing kernel. -/
def ownerGluingEmbedding {Q Old : Type v}
    (R : OwnerGluingKernel Q Old) (q : Q) :
    Old ↪ Quotient R.relation where
  toFun x := Quotient.mk R.relation (q, x)
  inj' := by
    intro x y h
    exact R.sameOwner q x y (Quotient.exact h)

/-- Equality of quotient vertices is exactly the given cross-owner
identification relation; no unintended equalities are introduced. -/
theorem ownerGluingEmbedding_eq_iff {Q Old : Type v}
    (R : OwnerGluingKernel Q Old)
    (q r : Q) (x y : Old) :
    ownerGluingEmbedding R q x = ownerGluingEmbedding R r y ↔
      R.relation.r (q, x) (r, y) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Every actual system of injective standard-copy maps determines
a canonical gluing relation on all tagged old vertices. -/
def ownerGluingKernelOfMaps {Q Old W : Type v}
    (φ : Q → Old ↪ W) : OwnerGluingKernel Q Old where
  relation :=
    { r := fun a b => φ a.1 a.2 = φ b.1 b.2
      iseqv := by
        constructor
        · intro a
          rfl
        · intro a b h
          exact h.symm
        · intro a b c hab hbc
          exact hab.trans hbc }
  sameOwner := by
    intro q x y h
    exact (φ q).injective h

/-- Every actual vertex is recovered by evaluating its canonical
owner-tagged quotient class. -/
def ownerGluingToHost {Q Old W : Type v}
    (φ : Q → Old ↪ W) :
    Quotient (ownerGluingKernelOfMaps φ).relation → W :=
  Quotient.lift (fun p : Q × Old => φ p.1 p.2)
    (by
      intro a b h
      exact h)

/-- The canonical quotient evaluates to the actual vertex
of its owner embedding. -/
@[simp] theorem ownerGluingToHost_mk {Q Old W : Type v}
    (φ : Q → Old ↪ W) (q : Q) (x : Old) :
    ownerGluingToHost φ
      (Quotient.mk (ownerGluingKernelOfMaps φ).relation (q, x)) =
        φ q x := rfl

/-- The map from the canonical owner quotient back to the
realised ambient union is injective: the quotient relation
was defined to be the exact physical equality kernel. -/
theorem ownerGluingToHost_injective {Q Old W : Type v}
    (φ : Q → Old ↪ W) :
    Function.Injective (ownerGluingToHost φ) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  apply Quotient.sound
  exact h

/-- If an arbitrary actual system of owner embeddings realizes a
specified gluing kernel exactly, its whole selected forest status
agrees with the canonical quotient model. A single global injection
from the old picture to the actual host is NOT required. -/
theorem forestOfCopies_ownerQuotient_iff
    {Q Old W C : Type v} [Fintype C]
    (P : C → HypergraphPiece Old) (owner : C → Q)
    (R : OwnerGluingKernel Q Old)
    (φ : Q → Old ↪ W)
    (hRealize : ∀ q r : Q, ∀ x y : Old,
      (φ q x = φ r y) ↔ R.relation.r (q, x) (r, y)) :
    ForestOfCopies (fun c => (P c).map (φ (owner c))) ↔
      ForestOfCopies
        (fun c => (P c).map (ownerGluingEmbedding R (owner c))) := by
  apply forestOfCopies_ownerMaps_iff_of_crossOwnerAgreement
    P owner φ (ownerGluingEmbedding R)
  intro c d x y
  exact (hRealize (owner c) (owner d) x y).trans
    (ownerGluingEmbedding_eq_iff R (owner c) (owner d) x y).symm

/-- Every already existing multi-owner standard-picture configuration
is forest-equivalent to the canonical quotient of its actual
cross-owner equality kernel. This supplies a normal form for fixed
finite configurations, not for the whole free successor reservoir. -/
theorem forestOfCopies_ownerQuotient_of_actualMaps
    {Q Old W C : Type v} [Fintype C]
    (P : C → HypergraphPiece Old) (owner : C → Q)
    (φ : Q → Old ↪ W) :
    ForestOfCopies (fun c => (P c).map (φ (owner c))) ↔
      ForestOfCopies (fun c => (P c).map
        (ownerGluingEmbedding (ownerGluingKernelOfMaps φ) (owner c))) := by
  apply forestOfCopies_ownerQuotient_iff P owner
    (ownerGluingKernelOfMaps φ) φ
  intro q r x y
  rfl

end StructuralRamsey.Girth
