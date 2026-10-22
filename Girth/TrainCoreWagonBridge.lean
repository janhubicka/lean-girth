import Girth.TrainCoreWagonEmbedding
import Girth.TrainGeneratedActualAllLevelRestriction

/-!
# Preserve the output wagon represented by a shared standard edge

If a standard edge a and the genuinely shared old edge s belong to
the same old wagon, their actual attached output classes coincide with
the output class of s's *core image*. The second theorem identifies
this class with the injective core-wagon embedding. In particular
the original output wagon W is not discarded when passing to a core
incidence witness.

The strong shared-subtrain hRel remains an explicit input. This is
the precise bridge needed by the two-standard branch of the geometric
wagon-cut theorem; it does not yet assemble that four-case cut lemma.
-/

namespace StructuralRamsey.Girth

open StructuralRamsey.RelStructure

universe u v
section CoreWagonBridge

variable {L : RelLanguage.{u}} {UA Old Core I : Type v}
variable (A : RelStructure L UA) (hA : A.Irreducible)
variable (B : RelStructure L Old) (S : Set Old)
variable (D : RelStructure L Core)
variable (f : I → RelStructure.Embedding (B.induce S) D)
variable {m : ℕ}
variable (oldTrain : EdgeTrainLevels (OldACarrierEdge A B) m)
variable (coreTrain : EdgeTrainLevels (OldACarrierEdge A D) m)
variable (hShared : ∀ i : I, Nonempty (SharedOldACarrierEdge A B S))
variable (hRel : ∀ κ : Fin (m + 1), ∀ i s t,
  oldTrain.rel κ
    (sharedOldACarrierInclusion A B S s)
    (sharedOldACarrierInclusion A B S t) ↔
  coreTrain.rel κ
    (sharedOldACarrierCoreEmbedding A B S D f i s)
    (sharedOldACarrierCoreEmbedding A B S D f i t))
variable (μ : Fin (m + 1))

local notation "inOld" => sharedOldACarrierInclusion A B S
local notation "inCore" => sharedOldACarrierCoreEmbedding A B S D f
local notation "Gen" => generatedActualASupportTrain
  A hA B S D f oldTrain coreTrain hShared
local notation "Eqv" => actualAPictureEdgeEquiv A hA B S D f
local notation "Std" => (fun (i : I) (a : OldACarrierEdge A B) =>
  Eqv (physicalStandardEdge inOld inCore i a))
local notation "CoreImage" => (fun (b : OldACarrierEdge A D) =>
  Eqv (physicalCoreEdge inOld I b))

include hRel

/-- The output wagon of a standard edge a is exactly that of the
core image of any genuinely shared edge in a's old wagon.
This equality is between labelled quotient classes; it never
identifies two wagons merely by equal vertex carriers. -/
theorem generatedActualASupportTrain_standard_shared_wagon_eq
    (i : I) (a : OldACarrierEdge A B)
    (s : SharedOldACarrierEdge A B S)
    (hOld : oldTrain.rel μ (inOld s) a) :
    Quotient.mk ((Gen).wagonSetoid μ) (Std i a) =
      Quotient.mk ((Gen).wagonSetoid μ) (CoreImage (inCore i s)) := by
  have hOldReverse : oldTrain.rel μ a (inOld s) :=
    (oldTrain.equivalent μ).symm hOld
  have hOutput :
      (Gen).rel μ (Std i a) (Std i (inOld s)) :=
    (generatedActualASupportTrain_restrict_standard
      A hA B S D f oldTrain coreTrain hRel hShared
      μ i a (inOld s)).2 hOldReverse
  apply Quotient.sound
  change (Gen).rel μ (Std i a) (CoreImage (inCore i s))
  simpa only [physicalStandardEdge_shared, physicalCoreEdge] using hOutput

/-- The preceding concrete output class is the injection of the
appropriate core witness wagon. The map uses preservation of the
old shared relation, which follows from the stronger hRel interface. -/
theorem generatedActualASupportTrain_standard_wagon_eq_coreEmbedding
    (i : I) (a : OldACarrierEdge A B)
    (s : SharedOldACarrierEdge A B S)
    (hOld : oldTrain.rel μ (inOld s) a) :
    Quotient.mk ((Gen).wagonSetoid μ) (Std i a) =
      generatedActualASupportTrain_coreWagonEmbedding
        A hA B S D f oldTrain coreTrain
        (fun κ j p q h => (hRel κ j p q).mp h)
        hShared μ
        (Quotient.mk (coreTrain.wagonSetoid μ) (inCore i s)) := by
  rw [generatedActualASupportTrain_coreWagonEmbedding_mk]
  exact generatedActualASupportTrain_standard_shared_wagon_eq
    A hA B S D f oldTrain coreTrain hShared hRel μ i a s hOld

/-- A standard-owned physical incidence whose parent is W keeps the
identity of that ORIGINAL wagon connector when transported through a
shared old edge. This avoids dropping W from an existential core tag. -/
theorem generatedActualASupportTrain_standard_parent_eq_coreEmbedding
    (i : I) (a : OldACarrierEdge A B)
    (s : SharedOldACarrierEdge A B S)
    (W : Quotient ((Gen).wagonSetoid μ))
    (hParent : Quotient.mk ((Gen).wagonSetoid μ) (Std i a) = W)
    (hOld : oldTrain.rel μ (inOld s) a) :
    W =
      generatedActualASupportTrain_coreWagonEmbedding
        A hA B S D f oldTrain coreTrain
        (fun κ j p q h => (hRel κ j p q).mp h)
        hShared μ
        (Quotient.mk (coreTrain.wagonSetoid μ) (inCore i s)) :=
  hParent.symm.trans
    (generatedActualASupportTrain_standard_wagon_eq_coreEmbedding
      A hA B S D f oldTrain coreTrain hShared hRel μ i a s hOld)

end CoreWagonBridge
end StructuralRamsey.Girth
