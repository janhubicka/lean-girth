import Girth.TrainRecursiveUniformAllColours

set_option autoImplicit false
set_option Elab.async false

/-!
# Uniformity in BOTH finite colour palettes and finite edge types

The full train Ramsey induction is over cutoff vectors, not over one
fixed edge structure. In particular, the manuscript's cutoff-two case
builds a shorter train whose new edge structure is the whole finite
EHN witness X, rather than the original coloured edge A. It applies
the lower-rank order assertion to this NEW edge structure and a palette
of size r ^ |E(X)|.

Consequently the concrete rank induction must quantify over all finite
ordered edge structures and all finite nonempty palettes BEFORE recursing.
The existing selected q>2 construction works separately for every A
and every finite palette. This module only lifts that already proved
conditional q>2 transition to the correct uniform statement.

All finite edge types and colour palettes may be represented in
Type 0 when the circulation theorem is specialized to finite data;
the predicates here retain arbitrary fixed carrier universe v.

No base-two, cutoff-two or forest-to-order construction is assumed to
have been proved. They remain explicit independent operator inputs.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v

/-- The forest assertion with the correct quantifier order: every
finite ordered edge type A and every finite nonempty palette are covered
by ONE theorem at the current cutoff vector. -/
def UniformSelectedPartiteForestAllInputs
    (L : RelLanguage.{u}) (t : List ℕ) : Prop :=
  ∀ {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure L UA),
    UniformSelectedPartiteForestAllColours A₀ t

/-- Same type/colour uniformity for the actual selected order witness,
which will be applied to the shorter train's newly constructed edge X. -/
def UniformSelectedPartiteOrderAllInputs
    (L : RelLanguage.{u}) (t : List ℕ) : Prop :=
  ∀ {UA : Type v} [LinearOrder UA] [Finite UA] [Nonempty UA]
    (A₀ : RelStructure L UA),
    UniformSelectedPartiteOrderAllColours A₀ t

/-- The cutoff-two palette can be enlarged to r^n for ANY new finite
ordered edge structure X. This is not a claim that an X-stage exists:
the universal order assertion is still a hypothesis. -/
theorem UniformSelectedPartiteOrderAllInputs.finPower
    (L : RelLanguage.{u}) (t : List ℕ)
    (h : UniformSelectedPartiteOrderAllInputs.{u, v} L t)
    {UA : Type v} (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (r n : ℕ) (hr : 0 < r) :
    letI : Nonempty (Fin (r ^ n)) := ⟨⟨0, pow_pos hr n⟩⟩
    UniformSelectedPartiteOrder A₀ t (Fin (r ^ n)) := by
  letI : Nonempty (Fin (r ^ n)) := ⟨⟨0, pow_pos hr n⟩⟩
  exact UniformSelectedPartiteOrderAllColours.finPower A₀ t (h A₀) r n hr

/-- The new q>2 rank step is pointwise in the current edge structure
and palette. Hence the already constructed selected lower HJ witness
and physical PictureStep give the uniformly quantified larger-cutoff
field, still only using strictly smaller cutoff ranks. -/
theorem uniformSelectedPartiteForestAllInputs_largerCutoff
    (L : RelLanguage.{u})
    (q : ℕ) (tail : List ℕ) (hq : 2 < q)
    (hAllLower : ∀ d : ℕ, 0 < d →
      UniformSelectedPartiteForestAllInputs.{u, v} L
        (List.replicate d (q - 1) ++ tail)) :
    UniformSelectedPartiteForestAllInputs.{u, v} L (q :: tail) := by
  intro UA _ _ _ A₀
  exact uniformSelectedPartiteForestAllColours_largerCutoff
    A₀ q tail hq (fun d hd => hAllLower d hd A₀)

/-- Correct universal operator signature for the manuscript's joint
forest/order recursion. No fixed palette or fixed edge structure is
silently carried across a cutoff-two shortening call. -/
def uniformSelectedPartiteAllInputsOperators
    (L : RelLanguage.{u})
    (baseTwo : UniformSelectedPartiteForestAllInputs.{u, v} L [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllInputs.{u, v} L t →
      UniformSelectedPartiteOrderAllInputs.{u, v} L t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedPartiteOrderAllInputs.{u, v} L tail →
      UniformSelectedPartiteForestAllInputs.{u, v} L (2 :: tail)) :
    Operators
      (UniformSelectedPartiteForestAllInputs.{u, v} L)
      (UniformSelectedPartiteOrderAllInputs.{u, v} L) where
  baseTwo := baseTwo
  forestToOrder := forestToOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hAllLower
    exact uniformSelectedPartiteForestAllInputs_largerCutoff
      L q tail hq hAllLower

/-- Correctly quantified conditional complete rank assembly. Three
additional geometric operators (base two, cutoff two, same-vector
forest-to-order) still have to be established. In particular the result
does not assert unrestricted FF_t without those premises. -/
theorem uniformSelectedPartiteForestAllInputs_of_remainingOperators
    (L : RelLanguage.{u})
    (baseTwo : UniformSelectedPartiteForestAllInputs.{u, v} L [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllInputs.{u, v} L t →
      UniformSelectedPartiteOrderAllInputs.{u, v} L t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedPartiteOrderAllInputs.{u, v} L tail →
      UniformSelectedPartiteForestAllInputs.{u, v} L (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForestAllInputs.{u, v} L t :=
  (uniformSelectedPartiteAllInputsOperators L
    baseTwo forestToOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness
