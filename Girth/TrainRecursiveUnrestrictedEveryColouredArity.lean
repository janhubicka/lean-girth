import Girth.TrainRecursiveUnrestrictedOrderInterface
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# Unrestricted selected order assertion at EVERY coloured-edge arity

The cutoff-two shorter-train construction replaces the old edge type
with one whose vertices are the entire EHN witness X. The exact relational
language colouredOrderedEdgeLanguage I k includes a k-ary edge symbol,
so this changes the language whenever the number of X vertices changes.

The already checked UniformSelectedUnrestrictedOrderAllInputs L t is
uniform over target structures, edge structures and finite palettes
for one FIXED language L. To use the lower-rank unrestricted order
assertion at the new k, the rank predicate must quantify over k (and
coarse predicate indices I) BEFORE recursion, not invent a
change-of-language transfer.

This definition only instantiates the existing corrected
EXISTENTIAL-BASE unrestricted order interface from Track 7.
It does not claim a proof of unrestricted RR_t, the same-vector
forest-to-order conversion, cutoff-two filling or base [2].
No identity-only base or false global X-partition is postulated.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v

/-- The actual unrestricted RR input across all finite coloured-edge
languages used by the circulation proof. A finite colour palette is
already quantified INSIDE UniformSelectedUnrestrictedOrderAllInputs,
after the arity and language are chosen. -/
def UniformSelectedUnrestrictedOrderEveryColouredArity
    (t : List ℕ) : Prop :=
  ∀ (I : Type u) [Finite I] [LinearOrder I]
    (k : ℕ) (hk : 2 ≤ k),
    UniformSelectedUnrestrictedOrderAllInputs.{u, v}
      (colouredOrderedEdgeLanguage I k) t

/-- Specialize the unrestricted order assertion at the literal new
hyperedge arity k=|V(X)|, independently of the eventual colour-word
length n=|E(X)|. The result still describes a genuinely chosen finite
Ramsey base and a selected OrderStage, not an identity-base picture. -/
theorem UniformSelectedUnrestrictedOrderEveryColouredArity.atArity
    (I : Type u) [Finite I] [LinearOrder I]
    (k : ℕ) (hk : 2 ≤ k) (t : List ℕ)
    (h : UniformSelectedUnrestrictedOrderEveryColouredArity.{u, v} t) :
    UniformSelectedUnrestrictedOrderAllInputs.{u, v}
      (colouredOrderedEdgeLanguage I k) t :=
  h I k hk

end StructuralRamsey.Girth.TrainRecursiveWitness
