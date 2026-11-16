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
This module lifts the kernel-verified conditional q>2 FOREST transition
to that statement. An unrestricted order assertion, with an actual
chosen Ramsey base, is handled separately; the obsolete partite-order
wrappers are deliberately omitted from this critical path.

All finite edge types and colour palettes may be represented in
Type 0 when the circulation theorem is specialized to finite data;
the predicates here retain arbitrary fixed carrier universe v.

No base-two, cutoff-two or unrestricted forest-to-order construction
is asserted here. These remain explicit independent obligations.
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

end StructuralRamsey.Girth.TrainRecursiveWitness
