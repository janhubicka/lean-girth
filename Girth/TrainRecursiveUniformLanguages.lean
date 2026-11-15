import Girth.TrainRecursiveUniformOperators
import Girth.TrainFillingColouredOrderedEdgePresentation

set_option autoImplicit false
set_option Elab.async false

/-!
# Uniformity in the ARITY of the coloured one-edge language

The manuscript's cutoff-two operation changes the coloured edge type:
the new single hyperedge has the WHOLE vertex set of the EHN witness X.
The concrete relational presentation colouredOrderedEdgeLanguage I k
uses a k-ary relation for edges. Its language changes when the number
of vertices of X differs from the old coloured-edge size.

The prior universal input wrappers quantify over all ordered source
A-structures and all finite palettes, but keep a FIXED RelLanguage L.
For the present k-ary language presentation, this is insufficient to
apply the shorter-train order theorem at a different edge size unless
one also proves a change-of-language transfer.

This module lifts the already-verified nontrivial q>2 partite forest
transition uniformly across EVERY finite-arity coloured-edge language.
No additional combinatorial lemma, new output existence hypothesis,
current-rank witness or unproved change-of-language transfer is used.

It does not prove base two, cutoff two, or the same-vector unrestricted
forest-to-order theorem. These remain explicit operators.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

universe u v

/-- Uniform selected forest assertion over every language L,
every finite ordered edge type A for that language and every finite
nonempty palette. The quantification over L takes place BEFORE the
rank recursion, unlike the fixed-L all-input assertion. -/
def UniformSelectedPartiteForestEveryLanguage
    (t : List ℕ) : Prop :=
  ∀ (L : RelLanguage.{u})
    {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure L UA)
    (κ : Type) [Fintype κ] [Nonempty κ],
      UniformSelectedPartiteForest A₀ t κ

/-- The already checked q>2 construction is pointwise in language,
edge structure and palette. Thus it fills the positive-depth rank
replacement for the language-uniform assertion without new geometry.
This is the actual universal quantifier order required for changing
the edge arity at a cutoff-two shortening. -/
theorem uniformSelectedPartiteForestEveryLanguage_largerCutoff
    (q : ℕ) (tail : List ℕ) (hq : 2 < q)
    (hLower : ∀ d : ℕ, 0 < d →
      UniformSelectedPartiteForestEveryLanguage.{u, v}
        (List.replicate d (q - 1) ++ tail)) :
    UniformSelectedPartiteForestEveryLanguage.{u, v} (q :: tail) := by
  intro L UA _ _ _ A₀ κ _ _
  exact uniformSelectedPartiteForest_largerCutoff A₀
    q tail hq κ (fun d hd => hLower d hd L A₀ κ)

/-- A concrete arity-k presentation is legitimately covered by the
language-uniform assertion, for any k, not just the old edge arity.
In the cutoff-two case one may take k = |V(X)|. -/
theorem UniformSelectedPartiteForestEveryLanguage.atColouredArity
    (I : Type u) (k : ℕ) (t : List ℕ)
    (h : UniformSelectedPartiteForestEveryLanguage.{u, v} t)
    {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure (colouredOrderedEdgeLanguage I k) UA)
    (κ : Type) [Fintype κ] [Nonempty κ] :
    UniformSelectedPartiteForest A₀ t κ :=
  h (colouredOrderedEdgeLanguage I k) A₀ κ

/-- The q>2 field is completely supplied for the LANGUAGE-UNIFORM
assertion. The other three operators are explicit mathematical inputs:
the actual [2] stage, same-vector transfer to an unrestricted order
assertion, and genuine cutoff-two filling at the shortened rank.
The auxiliary order predicate is deliberately left abstract, because
a fixed-L PARTITE order predicate is not unrestricted RR_tail. -/
def uniformEveryLanguageOperators
    (OrderWitness : List ℕ → Prop)
    (baseTwo : UniformSelectedPartiteForestEveryLanguage.{u, v} [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestEveryLanguage.{u, v} t →
      OrderWitness t)
    (cutoffTwo : ∀ tail, Admissible tail →
      OrderWitness tail →
      UniformSelectedPartiteForestEveryLanguage.{u, v} (2 :: tail)) :
    Operators (UniformSelectedPartiteForestEveryLanguage.{u, v})
      OrderWitness where
  baseTwo := baseTwo
  forestToOrder := forestToOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hLower
    exact uniformSelectedPartiteForestEveryLanguage_largerCutoff
      q tail hq hLower

/-- Conditional full-rank forest conclusion with changed-language
recursion supported. The three unproved base/order/cutoff operators
are exposed in the theorem, not silently discharged. -/
theorem uniformEveryLanguageForest_of_remainingOperators
    (OrderWitness : List ℕ → Prop)
    (baseTwo : UniformSelectedPartiteForestEveryLanguage.{u, v} [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestEveryLanguage.{u, v} t →
      OrderWitness t)
    (cutoffTwo : ∀ tail, Admissible tail →
      OrderWitness tail →
      UniformSelectedPartiteForestEveryLanguage.{u, v} (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForestEveryLanguage.{u, v} t :=
  (uniformEveryLanguageOperators OrderWitness
    baseTwo forestToOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness
