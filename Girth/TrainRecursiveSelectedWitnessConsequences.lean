import Girth.TrainRecursiveCoarsenedRamseyArrow
import Girth.TrainRecursiveFineWitnessBounds

set_option autoImplicit false
set_option Elab.async false

/-!
# Fine-witness local bounds inherited from an actual lower forest stage

The lower recursive witness carries more than a bare partite Ramsey arrow.
Its genuine selected labels, mixed irreducible coverage, and bottom mixed
forest imply several fields required by the next active attachment.

We preserve the literal selected-copy index subtype; no quotient by equal
vertex carriers is taken. The coarsened partite system retains the exact
relational reduct. This pass removes four otherwise independent local
hypotheses once an appropriate lower stage and a target A-coverage lemma
have been constructed.

It does NOT construct the lower stage, its larger partite base, the train
restriction or positive gluing-system girth certificates, or the attached
output supreme-cycle bound. The manuscript's final recursive existence
statement therefore remains open.
-/

namespace StructuralRamsey.Girth.TrainRecursiveWitness

open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P X I : Type v}

section StageConsequences

variable {A : RelStructure L UA} {B : RelStructure L VB}
variable {D : RelStructure L P}
variable {family : Set (Embedding B D)} {t : List ℕ}
variable {targetTrain : EdgeTrainLevels (OldACarrierEdge A B) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (S : ForestTailStage A B D family t targetTrain allowed)

/-- Restrict the actual bottom mixed forest to any family of genuinely
selected B-embeddings. Its index type may be arbitrary and need not be
inhabited. The cutoff may only decrease. No physical support edge is
deleted from the ambient picture. -/
theorem ForestTailStage.selectedEmbeddings_mixedForest
    (f : I → Embedding B S.system.toRelStructure)
    (hSelected : ∀ i, ∃ b : DesignatedCopy B D S.system family,
      b ∈ S.selected ∧ f i = b.embedding)
    (q : ℕ) (hq : q ≤ t.headD 0) :
    FiniteMixedForestThrough (RelationalMixedSupportTest A f) q := by
  intro s hTest hCard
  apply S.bottomForest s ?_ (hCard.trans hq)
  intro piece hp
  rcases hTest piece hp with ⟨i, hi⟩ | ⟨a, ha⟩
  · obtain ⟨b, hb, hfi⟩ := hSelected i
    exact Or.inr ⟨b, hb, by simpa only [hfi] using hi⟩
  · exact Or.inl ⟨a, ha⟩

/-- The lower stage's *mixed* irreducible coverage upgrades to ordinary
A-extension of every irreducible as soon as its target B has A-extension.
The B alternative is factored through its actual selected embedding, while
the ambient A alternative is already a witness. -/
theorem ForestTailStage.irreduciblesExtendTo_of_target
    (hTarget : IrreduciblesExtendTo A B) :
    IrreduciblesExtendTo A S.system.toRelStructure := by
  classical
  intro T hT
  rcases S.mixedCoverage T hT with ⟨b, _hb, hCover⟩ | ⟨a, ha⟩
  · let incT : Embedding (S.system.toRelStructure.induce T)
        S.system.toRelStructure :=
      RelStructure.inclusion S.system.toRelStructure T
    let eB : Embedding (S.system.toRelStructure.induce T) B :=
      incT.factorThroughRange b.embedding hCover
    have hIrr : (B.induce (Set.range eB)).Irreducible :=
      hT.range_embedding eB
    obtain ⟨c, hc⟩ := hTarget (Set.range eB) hIrr
    refine ⟨b.embedding.comp c, ?_⟩
    intro z
    obtain ⟨u, hu⟩ := hc ⟨eB z, ⟨z, rfl⟩⟩
    refine ⟨u, ?_⟩
    calc
      z.1 = b.embedding (eB z) := Classical.choose_spec (hCover z)
      _ = b.embedding (c u) := congrArg b.embedding hu
  · exact ⟨a, ha⟩

end StageConsequences

section CoarsenedFineWitness

variable (A : RelStructure L UA)
variable (Target : StructuralRamsey.Partite.System L UA VB)
variable (D : StructuralRamsey.Partite.System L UA P)
variable {family : Set (Embedding Target.toRelStructure D.toRelStructure)}
variable {t : List ℕ}
variable {targetTrain : EdgeTrainLevels
  (OldACarrierEdge A Target.toRelStructure) t.length}
variable {allowed : Fin (t.length + 1) → Set P}
variable (S : ForestTailStage A Target.toRelStructure D.toRelStructure
  family t targetTrain allowed)

/-- Four genuine fine-witness inputs follow from an actual larger-base
lower stage: partiteness, A-coverage, literal selected-index injectivity,
and the complete local mixed-forest bound through any smaller cutoff.

The partite gluing index is exactly the subtype of *selected labels*,
not an injection chosen from their vertex carriers. The assumptions
hD, hTargetCoverage and hFamilyParts describe the actual lower-stage
geometry; none is an output attachment bound or a fictitious witness. -/
theorem ForestTailStage.coarsenedSelected_fineWitnessInputs
    (hD : D.IsPartiteOver A)
    (hTargetCoverage : IrreduciblesExtendTo A Target.toRelStructure)
    (hFamilyParts : ∀ b, b ∈ family → ∀ x : VB,
      D.part (b x) = Target.part x)
    (q : ℕ) (hq : q ≤ t.headD 0) :
    (S.system.coarsenVia D S.isPartite).IsPartiteOver A ∧
    IrreduciblesExtendTo A
      (S.system.coarsenVia D S.isPartite).toRelStructure ∧
    Function.Injective (fun i : {b : DesignatedCopy
        Target.toRelStructure D.toRelStructure S.system family //
        b ∈ S.selected} =>
      bSupportPiece A
        ((selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite family hFamilyParts S.selected i).toEmbedding)) ∧
    FiniteMixedForestThrough
      (RelationalMixedSupportTest A (fun i :
        {b : DesignatedCopy
          Target.toRelStructure D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite family hFamilyParts S.selected i).toEmbedding)) q := by
  refine ⟨StructuralRamsey.Partite.System.coarsenVia_isPartiteOver
    D S.system A S.isPartite hD, ?_, ?_, ?_⟩
  · change IrreduciblesExtendTo A S.system.toRelStructure
    exact S.irreduciblesExtendTo_of_target hTargetCoverage
  · change Function.Injective (fun i : {b : DesignatedCopy
      Target.toRelStructure D.toRelStructure S.system family //
      b ∈ S.selected} => bSupportPiece A i.1.embedding)
    exact S.selectedPhysicalInjective
  · apply S.selectedEmbeddings_mixedForest
      (fun i : {b : DesignatedCopy
          Target.toRelStructure D.toRelStructure S.system family //
          b ∈ S.selected} =>
        (selectedPartiteGluingFamily_of_largeBase
          Target D S.system S.isPartite family hFamilyParts S.selected i).toEmbedding)
      ?_ q hq
    intro i
    exact ⟨i.1, i.2, rfl⟩

end CoarsenedFineWitness

end StructuralRamsey.Girth.TrainRecursiveWitness
