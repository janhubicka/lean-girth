import Girth.TrainRecursiveUniformLowerPictureStep
import Girth.TrainRecursiveHJFreshSelectedFinitePass

set_option autoImplicit false
set_option Elab.async false

/-!
# The actual q>2 operator for the universal nontrivial selected forest assertion

The larger-cutoff case of the train induction is obtained by one finite
pass through ALL profiles of the prescribed large base. Every nontrivial
profile's actual FirstWagonRefinement is chosen from the maintained
readiness invariant; its genuinely selected lower witness is obtained
from the strict lower-rank UNIVERSAL hypothesis, over the whole refined
true active source and a large Hales--Jewett base.

This is the first concrete replacement for the abstract
Operators.largerCutoff field. It does not provide the [2] base,
cutoff-two with nonempty tail, or a separate one-copy target case.
The result remains restricted to the genuine nontrivial, A-linear,
strong-family input domain explicitly recorded in
UniformSelectedPartiteForest.

No current-rank witness, current-rank operator, prechosen refinement,
selected lower witness, or output tail bound is an assumption.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA : Type v}

/-- Given the universal selected forest theorem at ALL lower vectors
of positive-depth repetitions of q-1, construct it at q::tail for q>2
in the actual nontrivial, linear strong-family regime.

The finite pass handles absent/single-edge fibres itself. Its only
nontrivial step is produced from the strict lower-rank assertion,
not supplied by the theorem statement. -/
theorem uniformSelectedPartiteForest_largerCutoff
    (A₀ : RelStructure L UA) [LinearOrder UA] [Finite UA] [Nonempty UA]
    (q : ℕ) (tail : List ℕ) (hq : 2 < q)
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (hAllLower : ∀ d : ℕ, 0 < d →
      UniformSelectedPartiteForest A₀
        (List.replicate d (q - 1) ++ tail) κ) :
    UniformSelectedPartiteForest A₀ (q :: tail) κ := by
  intro VB V hFiniteVB hFiniteV
    Target Large family ht hSource hSourceLinear hTargetTwo
    hLargePartite hLargeLinear hStrong hFamilyParts
    targetTrain fineAllowed hSupportNonempty hSupportCovers
    hGirth hParameters hTargetCuts hPartiteArrow
  letI : Finite VB := hFiniteVB
  letI : Finite V := hFiniteV
  exact constructFromPartiteTargetCuts_of_freshNontrivialRefiningSteps
    A₀ Target Large family hSource hFamilyParts
    (q :: tail) ht targetTrain fineAllowed
    hSupportNonempty hSupportCovers hGirth hParameters hTargetCuts
    (q - 1) κ hPartiteArrow
    (by
      intro e remaining S hFresh hPair hReady
      exact ForestTailStage.refiningPictureStep_of_uniformLowerRank
        A₀ Target.toRelStructure Large.toRelStructure
        S ht hq e hPair hLargeLinear hStrong hTargetTwo
        κ hAllLower remaining hFresh hReady)

end StructuralRamsey.Girth.TrainRecursiveWitness
