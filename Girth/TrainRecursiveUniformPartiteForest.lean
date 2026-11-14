import Girth.TrainRecursiveHJFreshSelectedFinitePass

set_option autoImplicit false
set_option Elab.async false

/-!
# A concrete, universal selected partite forest assertion

The abstract Operators recursion must be instantiated with an assertion
which works for EVERY genuine ordered A-partite target and EVERY finite
large base with a prescribed part-preserving family. Its lower-rank
hypothesis cannot be a single witness chosen for a particular processed
profile, and cannot assume an already constructed current-rank PictureStep.

This predicate packages exactly the target hypotheses and the actual
indexed selected arrow conclusion of the checked partite finite-pass
theorem, for one fixed ordered source A, cutoff vector and finite palette.

No theorem in this file asserts that the predicate is true: that is the
mathematical content still required of the well-founded induction.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA : Type v}

/-- Actual universal forest assertion at one cutoff vector.

Unlike the abstract Operators.ForestWitness placeholder, the target,
large base, lower allowed sets, selected family and resulting DesignatedArrow
are the literal physical data used in the circulation.  The assertion
quantifies over the entire target and base, and thus can be applied to a
new active subsystem at *strictly smaller rank* without assuming its
specific witness as an extra premise. -/
def UniformSelectedPartiteForest
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (t : List ℕ) (κ : Type w) [Nonempty κ] : Prop :=
  ∀ {VB V : Type v} [Finite VB] [Finite V]
    (Target : StructuralRamsey.Partite.System L.withOrder UA VB)
    (Large : StructuralRamsey.Partite.System L.withOrder UA V)
    (family : Set (Embedding
      Target.toRelStructure Large.toRelStructure))
    (ht : Admissible t)
    (hTargetPartite : Target.IsPartiteOver A₀.ordered)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      Large.part (b x) = Target.part x)
    (targetTrain : EdgeTrainLevels
      (OldACarrierEdge A₀.ordered Target.toRelStructure) t.length)
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (hSupportNonempty : Nonempty
      (OldACarrierEdge A₀.ordered Target.toRelStructure))
    (hSupportCovers : ∀ x : VB,
      ∃ a : OldACarrierEdge A₀.ordered Target.toRelStructure,
        x ∈ a.1)
    (hGirth : GirthGT
      (supportCopies A₀.ordered Target.toRelStructure) (t.headD 0))
    (hParameters : targetTrain.AdjacentParameters (fun e => e.1)
      (fun ν => Target.part ⁻¹' fineAllowed ν))
    (hTargetCuts : ∀ j : Fin t.length, 0 < j.val →
      LabelledGirthGT
        (targetTrain.wagonClassCarrier (fun e => e.1) j.castSucc)
        (t.get j))
    (hPartiteArrow : ∀ χ : StructuralRamsey.Partite.Embedding
        (StructuralRamsey.Partite.transversal A₀.ordered) Large → κ,
      ∃ b : StructuralRamsey.Partite.Embedding Target Large,
        b.toEmbedding ∈ family ∧
        ∀ a₁ a₂ : StructuralRamsey.Partite.Embedding
          (StructuralRamsey.Partite.transversal A₀.ordered) Target,
          χ (b.comp a₁) = χ (b.comp a₂)),
    ∃ S : ForestTailStage A₀.ordered Target.toRelStructure
      Large.toRelStructure family t targetTrain
      (fun ν => Large.part ⁻¹' fineAllowed ν),
      DesignatedArrow S κ

end StructuralRamsey.Girth.TrainRecursiveWitness
