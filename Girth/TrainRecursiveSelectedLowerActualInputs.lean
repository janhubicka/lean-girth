import Girth.TrainRecursiveSelectedWitnessConsequences
import Girth.TrainRecursiveCoarsenedSelectedRestriction
import Girth.TrainRecursiveCoarsenedStageParameters
import Girth.TrainRecursiveCanonicalFineAllowed

set_option autoImplicit false
set_option Elab.async false

/-!
# Complete reusable intrinsic inputs from an actual selected lower stage

The q>2 nontrivial-fibre PictureStep must use a TRUE lower selected
ForestTailStage. It has seven geometric/arrow data fields that can be
derived from the stage itself after canonical part coarsening, rather
than re-assumed for an abstract geometric witness.

These are: A-partiteness of the coarsened stage, irreducible A-coverage,
injectivity of the literal selected gluing label subtype, bottom mixed
forest, exact target fine-train restriction at every physical A-copy,
adjacent parameters for the coarsened A-parts, and the genuine PARTITE
family arrow obtained from the lower stage's RELATIONAL designated arrow.

The source lower target and large base are genuinely A-partite, every
prescribed base copy preserves A-parts, and the lower stage's allowed
sets are literal inverse images of selected fine A-part sets. No HJ
power high girth, label quotient or independent fine-witness data.

Separately, the actual FirstWagonRefinement's R.permitted_subset and
R.permitted_subsingleton fields supply all three canonical fine allowed
constraints required by the attachment. The remaining local geometry
is the positive FullSystemGirthGT, output SupremeCycleBound and actual
nontrivial-fibre selected lower Ramsey witness.
-/

namespace StructuralRamsey.Girth

universe v
variable {E W P UA : Type v}

/-- For the genuinely chosen first-wagon refinement, ALL three
canonical fine-allowed conditions required by the larger-cutoff
attachment follow from the actual refinement fields. No independent
singleton / first / retained allowed-set assumption is needed. -/
theorem FirstWagonRefinement.canonicalFineAllowed_all_constraints
    {m : ℕ} {T : EdgeTrainLevels E m} {hm : 0 < m}
    {edge : E → Set W} {part : W → P} {g : ℕ}
    (oldAllowed : Fin (m + 1) → Set P)
    (R : FirstWagonRefinement T hm edge part
      (oldAllowed ⟨1, Nat.succ_lt_succ hm⟩) g)
    (α : UA ↪ P) :
    (∀ j : Fin (R.extraCuts + 1),
      (TrainRecursiveWitness.fineAllowedFromRefinement
        m R.extraCuts hm α oldAllowed R.permitted
          (firstRefinementParent m R.extraCuts hm j)).Subsingleton) ∧
    (∀ ρ : Fin (m + R.extraCuts + 1),
      0 < ρ.val → ρ.val ≤ R.extraCuts + 1 →
      TrainRecursiveWitness.fineAllowedFromRefinement
        m R.extraCuts hm α oldAllowed R.permitted ρ ⊆
          α ⁻¹' oldAllowed ⟨1, Nat.succ_lt_succ hm⟩) ∧
    (∀ ν : Fin (m + 1), 0 < ν.val →
      TrainRecursiveWitness.fineAllowedFromRefinement
        m R.extraCuts hm α oldAllowed R.permitted
          (EdgeTrainLevels.firstForgetIndex m R.extraCuts ν) ⊆
        α ⁻¹' oldAllowed ν) := by
  exact TrainRecursiveWitness.fineAllowedFromRefinement_all_constraints
    m R.extraCuts hm α oldAllowed R.permitted
    R.permitted_subset R.permitted_subsingleton

end StructuralRamsey.Girth

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- Seven literal intrinsic fine-witness inputs, derived jointly
from an ACTUAL selected lower ForestTailStage over an A-partite
base. This is a conditional selected-STAGE theorem (stage and
DesignatedArrow must really exist), not a lower witness existence
assertion or a substitute for the output SupremeCycleBound. -/
theorem ForestTailStage.coarsenedSelected_actualLocalInputBundle
    (A : RelStructure L UA)
    (Target : StructuralRamsey.Partite.System L UA VB)
    (D : StructuralRamsey.Partite.System L UA P)
    (family : Set (Embedding Target.toRelStructure D.toRelStructure))
    {t : List ℕ}
    {targetTrain : EdgeTrainLevels
      (OldACarrierEdge A Target.toRelStructure) t.length}
    (fineAllowed : Fin (t.length + 1) → Set UA)
    (S : ForestTailStage A Target.toRelStructure D.toRelStructure
      family t targetTrain
      (fun ν => D.part ⁻¹' fineAllowed ν))
    (hD : D.IsPartiteOver A)
    (hTargetCoverage : IrreduciblesExtendTo A Target.toRelStructure)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (q : ℕ) (hq : q ≤ t.headD 0)
    (κ : Type w) [Nonempty κ]
    (hArrow : DesignatedArrow S κ) :
    let E := S.system.coarsenVia D S.isPartite
    let I := {b : DesignatedCopy
      Target.toRelStructure D.toRelStructure S.system family //
      b ∈ S.selected}
    let f : I → StructuralRamsey.Partite.Embedding Target E :=
      fun i => selectedPartiteGluingFamily_of_largeBase
        Target D S.system S.isPartite family hFamilyParts
        S.selected i
    E.IsPartiteOver A ∧
      IrreduciblesExtendTo A E.toRelStructure ∧
      Function.Injective (fun i : I =>
        bSupportPiece A ((f i).toEmbedding)) ∧
      FiniteMixedForestThrough
        (RelationalMixedSupportTest A (fun i : I => (f i).toEmbedding)) q ∧
      (∀ (ν : Fin (t.length + 1)) (i : I)
        (a b : Embedding A Target.toRelStructure),
        S.train.rel ν
          (actualEdge ((f i).toEmbedding.comp a))
          (actualEdge ((f i).toEmbedding.comp b)) ↔
        targetTrain.rel ν (actualEdge a) (actualEdge b)) ∧
      S.train.AdjacentParameters (fun edge => edge.1)
        (fun ν => E.part ⁻¹' fineAllowed ν) ∧
      StructuralRamsey.Partite.Arrow
        (StructuralRamsey.Partite.transversal A) Target E κ := by
  let E := S.system.coarsenVia D S.isPartite
  let I := {b : DesignatedCopy
    Target.toRelStructure D.toRelStructure S.system family //
    b ∈ S.selected}
  let f : I → StructuralRamsey.Partite.Embedding Target E :=
    fun i => selectedPartiteGluingFamily_of_largeBase
      Target D S.system S.isPartite family hFamilyParts
      S.selected i
  have hBasics := S.coarsenedSelected_fineWitnessInputs
    A Target D hD hTargetCoverage hFamilyParts q hq
  refine ⟨hBasics.1, hBasics.2.1, hBasics.2.2.1,
    hBasics.2.2.2, ?_, ?_, ?_⟩
  · intro ν i a b
    exact S.coarsenedSelected_trainRestriction
      A Target D hFamilyParts ν i a b
  · exact S.coarsened_adjacentParameters_preimage
      A Target.toRelStructure D fineAllowed
  · exact S.partiteArrow_after_largeBaseCoarsen
      A Target D family hFamilyParts κ hArrow

end StructuralRamsey.Girth.TrainRecursiveWitness
