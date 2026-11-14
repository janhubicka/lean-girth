import Girth.TrainRecursiveUniformLargerCutoff
import Girth.TrainRecursiveWitness

set_option autoImplicit false
set_option Elab.async false

/-!
# Concrete forest/order predicates and the actual larger-cutoff Operators field

The abstract well-founded recursion in TrainRecursiveWitness only becomes
the circulation theorem once its two witness predicates have an exact
mathematical meaning and its operators are concrete constructions.

The forest predicate is UniformSelectedPartiteForest, whose genuine
q>2 transition is proved in TrainRecursiveUniformLargerCutoff. The order
predicate below uses the same actual finite input and a REAL OrderStage,
carrying full system-girth at all cuts and a selected DesignatedArrow.

The operator constructor DISCHARGES the entire q>2 field by the real
rank-lower picture construction. It exposes exactly three still-needed
non-q>2 mathematical inputs: the [2] selected forest base, the
same-vector forest-to-order theorem, and the cutoff-two filling theorem.

Nothing in this file assumes a current-rank q>2 witness or fabricates
OrderStage / DesignatedArrow data.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {UA : Type v}

/-- Universal selected order assertion at a prescribed cutoff vector.
Its target and large-base inputs are exactly those of the forest
assertion, but the output is an actual OrderStage with full cut girth. -/
def UniformSelectedPartiteOrder
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
    (hTargetLinear : ALinear A₀.ordered Target.toRelStructure)
    (hTargetTwo : ∃ a b : Embedding A₀.ordered Target.toRelStructure,
      ¬ SameCopy a b)
    (hLargePartite : Large.IsPartiteOver A₀.ordered)
    (hLargeLinear : ALinear A₀.ordered Large.toRelStructure)
    (hFamilyStrong : ∀ b, b ∈ family →
      AStrong A₀.ordered Large.toRelStructure (copyCarrier b))
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
    ∃ S : OrderStage A₀.ordered Target.toRelStructure
      Large.toRelStructure family t targetTrain
      (fun ν => Large.part ⁻¹' fineAllowed ν),
      DesignatedArrow S.toForestTailStage κ

/-- The genuine nontrivial q>2 construction fills the largerCutoff
field of the actual universal forest/order induction. The three
remaining operator fields are stated as explicit mathematical inputs,
not implicit current-rank witnesses. -/
def uniformSelectedPartiteOperators
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (baseTwo : UniformSelectedPartiteForest A₀ [2] κ)
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForest A₀ t κ →
      UniformSelectedPartiteOrder A₀ t κ)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedPartiteOrder A₀ tail κ →
      UniformSelectedPartiteForest A₀ (2 :: tail) κ) :
    Operators
      (fun t => UniformSelectedPartiteForest A₀ t κ)
      (fun t => UniformSelectedPartiteOrder A₀ t κ) where
  baseTwo := baseTwo
  forestToOrder := forestToOrder
  cutoffTwo := cutoffTwo
  largerCutoff := by
    intro q tail _ hq hAllLower
    exact uniformSelectedPartiteForest_largerCutoff
      A₀ q tail hq κ hAllLower

/-- Conditional final forest theorem with the entire q>2 operator
DISCHARGED. The remaining premises are precisely the still-unproved
base-two, forest-to-order and cutoff-two mathematical constructions. -/
theorem uniformSelectedPartiteForest_of_remainingOperators
    (A₀ : RelStructure L UA)
    [LinearOrder UA] [Finite UA] [Nonempty UA]
    (κ : Type w) [Fintype κ] [Nonempty κ]
    (baseTwo : UniformSelectedPartiteForest A₀ [2] κ)
    (forestToOrder : ∀ t, Admissible t →
      UniformSelectedPartiteForest A₀ t κ →
      UniformSelectedPartiteOrder A₀ t κ)
    (cutoffTwo : ∀ tail, Admissible tail →
      UniformSelectedPartiteOrder A₀ tail κ →
      UniformSelectedPartiteForest A₀ (2 :: tail) κ)
    (t : List ℕ) (ht : Admissible t) :
    UniformSelectedPartiteForest A₀ t κ :=
  (uniformSelectedPartiteOperators A₀ κ
    baseTwo forestToOrder cutoffTwo).assemble t ht

end StructuralRamsey.Girth.TrainRecursiveWitness
