import Girth.TrainRecursiveExactHeightTransport
import Girth.TrainActiveGluingWitness

set_option autoImplicit false
set_option Elab.async false

/-!
# Full-system-girth transported across an exact train height equality

A true lower recursive train may be indexed by the list length
of its replicated cutoff vector, while the actual attachment
requires the arithmetically equal old height plus extra cuts.

The same physical train is transported by EdgeTrainLevels.castHeight.
Every gluing copy, ambient physical A-edge, quotient wagon and entire
simultaneous supreme-cycle bound is unchanged. The only operation
is a Fin coordinate cast along the equality of natural heights.
This does NOT weaken the requested numeric cutoff, and it does not
construct any new lower witness.

This is a primitive equality-transport theorem, not an assumption
of the output girth conclusion. Circulation only.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {UA P X Y I : Type v}

/-- The exact same actual gluing FullSystemGirthGT survives a proof
that the physical train has two equal height expressions. The original
cutoff q is preserved, with no new edge or label. -/
theorem activeGluingWitness_fullSystemGirth_castHeight
    (A : RelStructure L UA)
    (C : StructuralRamsey.Partite.System L P X)
    (α : UA → P) (R : RelStructure L Y)
    (f : I → Embedding
      (C.toRelStructure.induce (activeCarrier A C α)) R)
    {m n : ℕ}
    (T : EdgeTrainLevels (OldACarrierEdge A R) m)
    (h : m = n) (ν : Fin (n + 1)) (q : ℕ)
    (hOld :
      (activeGluingWitnessOrderOneData A C α R f T
        (Fin.cast (congrArg (fun k : ℕ => k + 1) h).symm ν)
      ).FullSystemGirthGT q) :
    (activeGluingWitnessOrderOneData A C α R f
      (T.castHeight h) ν).FullSystemGirthGT q := by
  cases h
  exact hOld

end StructuralRamsey.Girth
