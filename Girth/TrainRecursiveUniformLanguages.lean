import Girth.TrainRecursiveUniformOperators
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# Uniformity in the ARITY of the coloured one-edge language

The manuscript's cutoff-two operation changes the coloured edge type:
the new single hyperedge has the WHOLE vertex set of the EHN witness X.
The concrete relational presentation colouredOrderedEdgeLanguage I k
uses a k-ary relation for edges, so its language changes when the
number of vertices of X differs from the old coloured-edge size.

The earlier universal input wrappers quantify over all ordered source
A-structures and all finite palettes, but keep a FIXED language L.
For this k-ary edge presentation the shorter-train step needs an
additional quantifier over k, not an unexplained change-of-language
transfer. The number and ordering of coarse unary predicate names I
may be held fixed in one application, but we quantify over all finite
ordered I before recursing as well.

This module lifts the verified nontrivial q>2 partite forest transition
pointwise over all k and all finite ordered unary-predicate index sets.
It does NOT require base-two, cutoff-two or same-vector order conversion,
and does not assert a theorem for arbitrary non-coloured relational
languages beyond what the manuscript needs.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v

/-- Universal forest assertion for every finite coloured one-edge ARITY.
All finite ordered coloured-edge types and palettes are quantified over
BEFORE the rank recursion. There is no fixed k in the inductive type. -/
def UniformSelectedPartiteForestEveryColouredArity
    (t : List ℕ) : Prop :=
  ∀ (I : Type u) [Finite I] [LinearOrder I] (k : ℕ)
    {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure (colouredOrderedEdgeLanguage I k) UA)
    (κ : Type) [Fintype κ] [Nonempty κ],
      UniformSelectedPartiteForest A₀ t κ

/-- The checked q>2 construction is pointwise in the language, source
edge type and palette. Its strict smaller-rank step therefore remains
valid when the language can vary with the coloured edge arity k. -/
theorem uniformSelectedPartiteForestEveryColouredArity_largerCutoff
    (q : ℕ) (tail : List ℕ) (hq : 2 < q)
    (hLower : ∀ d : ℕ, 0 < d →
      UniformSelectedPartiteForestEveryColouredArity.{u, v}
        (List.replicate d (q - 1) ++ tail)) :
    UniformSelectedPartiteForestEveryColouredArity.{u, v}
      (q :: tail) := by
  intro I _ _ k UA _ _ _ A₀ κ _ _
  exact uniformSelectedPartiteForest_largerCutoff A₀
    q tail hq κ (fun d hd => hLower d hd I k A₀ κ)

/-- A concrete k-ary coloured ordered edge type is covered directly
for ANY k. In cutoff two, k is the number of VERTICES of the EHN
witness X, NOT the number of its original smaller hyperedges. -/
theorem UniformSelectedPartiteForestEveryColouredArity.atArity
    (I : Type u) [Finite I] [LinearOrder I]
    (k : ℕ) (t : List ℕ)
    (h : UniformSelectedPartiteForestEveryColouredArity.{u, v} t)
    {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure (colouredOrderedEdgeLanguage I k) UA)
    (κ : Type) [Fintype κ] [Nonempty κ] :
    UniformSelectedPartiteForest A₀ t κ :=
  h I k A₀ κ

/-- In the cutoff-two construction the new hyperedge arity k and the
length n of an original-edge colour word are INDEPENDENT parameters:
k = |V(X)| while n = |E(X)|. An r-colour word is a function
Fin n → Fin r. The universal assertion specializes to this literal
finite function palette at the NEW coloured edge arity without an
extra palette-amplification or language-transfer assumption. -/
theorem UniformSelectedPartiteForestEveryColouredArity.atColourWord
    (I : Type u) [Finite I] [LinearOrder I]
    (k n r : ℕ) (hr : 0 < r) (t : List ℕ)
    (h : UniformSelectedPartiteForestEveryColouredArity.{u, v} t)
    {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure (colouredOrderedEdgeLanguage I k) UA) :
    UniformSelectedPartiteForest A₀ t (Fin n → Fin r) := by
  letI : Nonempty (Fin n → Fin r) := ⟨fun _ => ⟨0, hr⟩⟩
  exact h I k A₀ (Fin n → Fin r)

/-- The entire q>2 operator field is supplied in the exact coloured
edge arity-uniform assertion. The OTHER fields explicitly demand:
the base [2], a forest-to-UNRESTRICTED-order assertion at the same
vector, and cutoff-two filling on a shorter train whose arity
may differ from that of the input. An arbitrary OrderWitness predicate
is used here, rather than incorrectly substituting partite RR. -/
def uniformEveryColouredArityOperators
    (OrderWitness : List ℕ → Prop)
    (baseTwo :
      UniformSelectedPartiteForestEveryColouredArity.{u, v} [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestEveryColouredArity.{u, v} t →
      OrderWitness t)
    (cutoffTwo : ∀ tail, Admissible tail →
      OrderWitness tail →
      UniformSelectedPartiteForestEveryColouredArity.{u, v}
        (2 :: tail)) :
    Operators (UniformSelectedPartiteForestEveryColouredArity.{u, v})
      OrderWitness where
  baseTwo := baseTwo
  forestToOrder := forestToOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hLower
    exact uniformSelectedPartiteForestEveryColouredArity_largerCutoff
      q tail hq hLower

/-- Conditional rank assembly with correctly varying coloured edge
arity, holding neither a fixed language nor a fixed colour palette.
All three remaining operator fields are visible in the statement. -/
theorem uniformEveryColouredArityForest_of_remainingOperators
    (OrderWitness : List ℕ → Prop)
    (baseTwo :
      UniformSelectedPartiteForestEveryColouredArity.{u, v} [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestEveryColouredArity.{u, v} t →
      OrderWitness t)
    (cutoffTwo : ∀ tail, Admissible tail →
      OrderWitness tail →
      UniformSelectedPartiteForestEveryColouredArity.{u, v}
        (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForestEveryColouredArity.{u, v} t :=
  (uniformEveryColouredArityOperators OrderWitness
    baseTwo forestToOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness
