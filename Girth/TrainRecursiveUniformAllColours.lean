import Girth.TrainRecursiveUniformOperators

set_option autoImplicit false
set_option Elab.async false

/-!
# Colour-uniform rank induction for the actual selected train witnesses

The train induction cannot fix one colour palette once and for all.
At the cutoff-two step the shorter-train Ramsey theorem is applied
with a palette of functions from the finite EHN edge set to the original
palette, typically of cardinality r ^ |E(X)|.

The existing fixed-palette q>2 construction is mathematically valid as a
local induction step: it only needs the same palette at strictly smaller
rank. To assemble *all* cutoffs, however, the forest and order predicates
must quantify over every finite nonempty palette, so that the cutoff-two
operator may invoke the tail theorem with an enlarged palette.

All finite palettes may be represented by finite types in Type 0, e.g.
Fin r, including every power palette needed in the manuscript. This
module strengthens only the induction interface; it does NOT prove the
remaining base-two, cutoff-two or same-vector order operators.

The lower selected stages and exact designated arrows are still obtained
by the existing genuinely selected q>2 construction. No new witness,
higher-girth assumption or current-rank local operator is introduced.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA : Type v}

/-- The actual selected forest assertion at every finite nonempty
colour type, not merely at one palette fixed before the rank induction. -/
def UniformSelectedPartiteForestAllColours
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (t : List ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [Nonempty κ],
    UniformSelectedPartiteForest A₀ t κ

/-- The same palette-uniform strengthening of the selected order assertion.
In particular, a later cutoff-two step may ask for the tail theorem with
a function-valued finite palette. -/
def UniformSelectedPartiteOrderAllColours
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (t : List ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [Nonempty κ],
    UniformSelectedPartiteOrder A₀ t κ

/-- The exact larger palette required in the cutoff-two filling
proof: r colours of each of n old edges become r^n finite colours.
This is direct specialisation of the universal order predicate, not
an unproved fixed-colour Ramsey amplification lemma. -/
theorem UniformSelectedPartiteOrderAllColours.finPower
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (t : List ℕ)
    (h : UniformSelectedPartiteOrderAllColours A₀ t)
    (r n : ℕ) (hr : 0 < r) :
    letI : Nonempty (Fin (r ^ n)) := ⟨⟨0, pow_pos hr n⟩⟩
    UniformSelectedPartiteOrder A₀ t (Fin (r ^ n)) := by
  exact h (Fin (r ^ n))

/-- The *real* larger-cutoff proof from the previous module preserves
universal quantification over palettes. The only induction calls are
at strictly smaller repeated-(q-1) vectors of positive depth. -/
theorem uniformSelectedPartiteForestAllColours_largerCutoff
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (q : ℕ) (tail : List ℕ) (hq : 2 < q)
    (hAllLower : ∀ d : ℕ, 0 < d →
      UniformSelectedPartiteForestAllColours A₀
        (List.replicate d (q - 1) ++ tail)) :
    UniformSelectedPartiteForestAllColours A₀ (q :: tail) := by
  intro κ _ _
  exact uniformSelectedPartiteForest_largerCutoff A₀ q tail hq κ
    (fun d hd => hAllLower d hd κ)

/-- The chosen induction operators quantify over the full finite palette
before recursing. This fixes the colour-amplification mismatch between the
fixed-palette interface and the original cutoff-two construction.

The three remaining mathematical fields are still explicit. In
particular, cutoffTwo must actually construct the selected filled stage. -/
def uniformSelectedPartiteAllColoursOperators
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (baseTwo : UniformSelectedPartiteForestAllColours A₀ [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllColours A₀ t →
      UniformSelectedPartiteOrderAllColours A₀ t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedPartiteOrderAllColours A₀ tail →
      UniformSelectedPartiteForestAllColours A₀ (2 :: tail)) :
    Operators
      (UniformSelectedPartiteForestAllColours A₀)
      (UniformSelectedPartiteOrderAllColours A₀) where
  baseTwo := baseTwo
  forestToOrder := forestToOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hAllLower
    exact uniformSelectedPartiteForestAllColours_largerCutoff
      A₀ q tail hq hAllLower

/-- Conditional rank assembly in the palette-uniform form needed by the
manuscript. The proof does not add any new operator as a hypothesis and
does not claim the three unsolved operators have been constructed. -/
theorem uniformSelectedPartiteForestAllColours_of_remainingOperators
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (baseTwo : UniformSelectedPartiteForestAllColours A₀ [2])
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForestAllColours A₀ t →
      UniformSelectedPartiteOrderAllColours A₀ t)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedPartiteOrderAllColours A₀ tail →
      UniformSelectedPartiteForestAllColours A₀ (2 :: tail))
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForestAllColours A₀ t :=
  (uniformSelectedPartiteAllColoursOperators A₀
    baseTwo forestToOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness
