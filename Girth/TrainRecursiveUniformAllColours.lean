import Girth.TrainRecursiveUniformLargerCutoff

set_option autoImplicit false
set_option Elab.async false

/-!
# Colour-uniform rank induction for the actual selected train witnesses

The train induction cannot fix one colour palette once and for all.
At the cutoff-two step the shorter-train Ramsey theorem is applied
with a palette of functions from the finite EHN edge set to the original
palette, typically of cardinality r ^ |E(X)|.

The existing fixed-palette q>2 construction is mathematically valid:
it only requests strictly lower-rank witnesses at the same palette.
For the full recursion, the forest predicate must quantify over every
finite nonempty palette BEFORE applying the cutoff-rank induction.
The unrestricted order predicate is defined separately and is not
replaced by a partite-order assertion.

All finite palettes may be represented by types in Type 0, e.g.
Fin r or Fin n → Fin r. This module preserves only the essential
palette-uniform FOREST q>2 operator, not the now-obsolete conditional
partite-order operators. Nothing proves the base-two, cutoff-two or
unrestricted same-vector forest-to-order steps.

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

end StructuralRamsey.Girth.TrainRecursiveWitness
